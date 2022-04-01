/*
 all constraints  are transformed with delta to linear arithmetic lazily
 */
package edu.melbourne.MAsat;

import com.microsoft.z3.ArithExpr;
import com.microsoft.z3.BoolExpr;
import com.microsoft.z3.Context;
import com.microsoft.z3.Expr;
import com.microsoft.z3.IntExpr;
import com.microsoft.z3.IntNum;
import com.microsoft.z3.Model;
import com.microsoft.z3.Solver;
import com.microsoft.z3.Status;
import com.microsoft.z3.Z3Exception;
import gurobi.GRB;
import gurobi.GRBEnv;
import gurobi.GRBException;
import gurobi.GRBLinExpr;
import gurobi.GRBModel;
import gurobi.GRBVar;
import java.io.FileWriter;
import java.util.ArrayList;
import java.util.Arrays;
import java.util.HashMap;
import java.util.HashSet;
import java.util.Iterator;
import java.util.Set;

/**
 *
 * @author kafle
 */
public class SATBendersDecompLazy {

    HashMap<String, TransformedFormula> transformedFormulas;
    HashMap<IntExpr, GRBVar> z3GRBVarMap;
    int counter; //counts the number of delta introduced
    int refinementCount;
    int disjointRefinementCount;
    int nrConstraintRelaxed;
    boolean deltaGenerated;
    IntExpr lastDelta;
    HashSet<IntExpr> boundedVars;
    HashSet<IntExpr> vars;
    GRBVar[] grbVars;
    int formulaCount;
    IntExpr[] deltas;
    boolean deltaValuesModified;
    HashMap<String, BoolExpr> idStringToBoolExpr;
    String[] currentAssumptions;
    String[] previousAssumptions;
    BoolExpr cutAssumptions;
    static final int PRINT_FLAG = 0; //0=do not print, any other number print
    static final int COEFF_THRESHOLD = 500;

    public void initialize() {
        counter = 1;
        transformedFormulas = new HashMap<>();
        refinementCount = 0;
        disjointRefinementCount = 0;
        nrConstraintRelaxed = 0;
        deltaGenerated = false; //no delta expr has been generated
        boundedVars = new HashSet<>();
        vars = new HashSet<>();
        formulaCount = 0;
        deltaValuesModified = false;
        idStringToBoolExpr = new HashMap<>();
    }

    public void dispose() {
        transformedFormulas = null;
        boundedVars = null;
        vars = null;
        z3GRBVarMap = null;
        grbVars = null;
        deltas = null;
        idStringToBoolExpr = null;
    }

    public Witness solveMixedLiaFormula(GRBModel grbModel, Context context, Z3Interface z3Interface, GurobiInterface grbInterface) {
        Witness arithWitness = solveArithFormula(grbModel, context, z3Interface, grbInterface);
        if (arithWitness.isSatisfiable()) {
//            if (allTransformed()) {
//                System.out.println("all constraints are transformed====== ");
//                return arithWitness;
//            }
//             grbInterface.grbWrite(grbModel, "out.sol");
            Util.print(PRINT_FLAG, "checking ma model");
            Witness maWitness = maModelWModuloZ3(arithWitness.getModel(), context, grbInterface, z3Interface); //returns sat or unsat_core
            Util.print(PRINT_FLAG, "cheked ma model");
            return maWitness;
        }
        return arithWitness;
    }

    public Witness solveArithFormula(GRBModel grbModel, Context ctx, Z3Interface z3Interface, GurobiInterface grbInterface) {
        grbInterface.resetModel(grbModel);
        Util.print(PRINT_FLAG, "calling gurobi");
        int status = grbInterface.optimize(grbModel);
        Util.print(PRINT_FLAG, "gurobi returned");

        if (status == GRB.Status.INFEASIBLE) {
            Util.print(PRINT_FLAG, "querying unsat core");
            String[] unsatCore = grbInterface.getUnsatCore(grbModel); // = currentAssumptions;
            Util.print(PRINT_FLAG, "unsat core returned");
            Util.print(PRINT_FLAG, "unsat core:  " + Message.printUnsatCore(unsatCore));
            return new Witness(false, null, unsatCore);
        } else if (status == GRB.Status.OPTIMAL) {
            return new Witness(true, grbModel, null);
        } else {
            System.out.println("solver returned unknown status..................");
            return null; // solver error
        }
    }

    /**
     * changes grbModel to Z3Model returns null if any of the var takes
     * non-integer solution
     */
    public Model getZ3ModelFrom(GRBModel grbModel, Context ctx) {
        Model z3Model;
        Solver z3Solver = ctx.mkSolver();
        GRBVar[] grbVars = grbModel.getVars();
        String varName;
        long varValue;
        IntExpr z3Var;
        IntNum z3Value;
        for (GRBVar v : grbVars) {
            try {
                varName = v.get(GRB.StringAttr.VarName);
                double d = v.get(GRB.DoubleAttr.X);
//                System.out.println("var value "+varName+" "+d);
                varValue = (long) d;
                if (d % 1 != 0) { //this means it is not an integer solution
                    return null;
                }
                z3Var = ctx.mkIntConst(varName);
                z3Value = ctx.mkInt(varValue);
                z3Solver.add(ctx.mkEq(z3Var, z3Value));
            } catch (GRBException ex) {
                ex.printStackTrace();
            }
        }
        z3Solver.check();
        z3Model = z3Solver.getModel(); //definitely gonna have a model
        return z3Model;
    }

    /**
     * checking whether a Z-model is a Z_m model using Z3
     */
    public Witness maModelWModuloZ3(GRBModel grbModel, Context ctx, GurobiInterface grbInterface, Z3Interface z3Interface) {
        Model m = getZ3ModelFrom(grbModel, ctx);
        TransformedFormula tf;
        Set<String> unsatIds = new HashSet<>();
        if (m == null) {
//            for (String key : transformedFormulas.keySet()) {
            for (String key : currentAssumptions) {
                tf = transformedFormulas.get(key);
                //only enough to check non-relaxed formulas, since all other will be satisfied
                if (tf.getStatus() == 0) {
                    unsatIds.add(key);
                }
            }
            return new Witness(false, null, unsatIds.toArray(new String[unsatIds.size()]));
        }
        BoolExpr maExpr = null;
        ArrayList<String> conflictConstr = new ArrayList<>();
//        for (String key: transformedFormulas.keySet()) {
        for (String key : currentAssumptions) {
//             System.out.println("key "+key);
            tf = transformedFormulas.get(key);
            //only enough to check non-relaxed formulas, since all other will be satisfied
            if (tf.getStatus() == 0) {
                maExpr = tf.getFormulaWModulo();
                //System.out.println("maexpr "+maExpr);
                Expr s = z3Interface.evalExprInModelWoMc(m, maExpr);
                //System.out.println("eval expr "+s);
                if (!s.isTrue()) {
                    conflictConstr.add(key);
                }
            }
        }
        int size = conflictConstr.size();
        if (size == 0) {
//            System.out.println("=================== ma_sat =========== ");
            // Util.print(PRINT_FLAG, "model "+m);
            return new Witness(true, grbModel, null);
        } else {
//            System.out.println("fake unsat core");
            return new Witness(false, null, conflictConstr.toArray(new String[size]));
        }
    }

    /**
     * checking whether a Z-model is a Z_m model using Gurobi
     */
    public Witness maModelWModuloGRB(GRBModel grbModel, Context ctx, GurobiInterface grbInterface) {
        //getZ3ModelFrom( grbModel,  ctx);
        BoolExpr maExpr = null;
        TransformedFormula tf;
        String arithOperator = "";
        GRBLinExpr grbE1 = null, grbE2 = null;
        ArrayList<String> conflictConstr = new ArrayList<>();
        for (String key : transformedFormulas.keySet()) {
            tf = transformedFormulas.get(key);
            if (tf.getStatus() == 0) { //transformed are already evaluated under modulo
                maExpr = tf.getOriginalFormula();
                //only enough to check non-relaxed formulas, since all other will be satisfied
                Expr[] exprs = maExpr.getArgs();
                if (maExpr.isGE()) {
                    arithOperator = ">=";
                    grbE1 = Util.z3Expr2GRBExpr((ArithExpr) exprs[0], grbModel, z3GRBVarMap);
                    grbE2 = Util.z3Expr2GRBExpr((ArithExpr) exprs[1], grbModel, z3GRBVarMap);

                } else if (maExpr.isLE()) {
                    arithOperator = "<=";
                    grbE1 = Util.z3Expr2GRBExpr((ArithExpr) exprs[0], grbModel, z3GRBVarMap);
                    grbE2 = Util.z3Expr2GRBExpr((ArithExpr) exprs[1], grbModel, z3GRBVarMap);

                } else if (maExpr.isEq()) {
                    arithOperator = "=";
                    grbE1 = Util.z3Expr2GRBExpr((ArithExpr) exprs[0], grbModel, z3GRBVarMap);
                    grbE2 = Util.z3Expr2GRBExpr((ArithExpr) exprs[1], grbModel, z3GRBVarMap);

                }
                Boolean evalRes = grbInterface.evalConstraintInModel(grbE1, arithOperator, grbE2);
                //System.out.println("eval expr "+s);
                if (evalRes == Boolean.FALSE) {
                    conflictConstr.add(key);
                    //System.out.println("============-====================check failed for clause " + key);
                }
            }
        }
        int size = conflictConstr.size();
        if (size == 0) {
//            System.out.println("=================== ma_sat =========== ");
            return new Witness(true, grbModel, null);
        } else {
            return new Witness(false, null, conflictConstr.toArray(new String[size]));
        }
    }

    public IntExpr nextDelta(Context ctx, int counter) {
        String s = "delta_" + Integer.toString(counter);
        IntExpr deltaExpr = (IntExpr) ctx.mkIntConst(s);
        lastDelta = deltaExpr;
        return deltaExpr;
    }

    public ArithExpr genDeltaExpr(Context ctx, String key) {
        IntExpr ie = nextDelta(ctx, counter);
        counter++;
        ArithExpr deltaExpr = ctx.mkMul(ctx.mkInt(Util.modulo_m()), ie);
        return deltaExpr;
    }

    public BoolExpr genVarsBounds(Context ctx, HashSet<IntExpr> vars, HashSet<IntExpr> alreadyBoundedVars) {
        BoolExpr acc = ctx.mkTrue();
        Iterator<IntExpr> itr = vars.iterator();
        while (itr.hasNext()) {
            IntExpr ie = itr.next();
            if (!alreadyBoundedVars.contains(ie)) {
                alreadyBoundedVars.add(ie);
                acc = ctx.mkAnd(acc, genVarBounds(ctx, ie));
            }
            //acc = ctx.mkAnd(acc, genVarBounds(ctx, ie));
        }
        return acc;
    }

    public BoolExpr genVarBounds(Context ctx, IntExpr var) {
        BoolExpr loBoundvar, upBoundvar;
        loBoundvar = ctx.mkLe((ArithExpr) ctx.mkInt(Util.min_neg()), var);
        upBoundvar = ctx.mkLe(var, (ArithExpr) ctx.mkInt(Util.max_pos()));
        return ctx.mkAnd(loBoundvar, upBoundvar);
    }

    /**
     * when both bounds coincide
     */
    public BoolExpr genDeltaBound(Context ctx, IntExpr delta, IntExpr bound) {
        return ctx.mkEq(delta, bound);
    }

    public BoolExpr genExprBounds(Context ctx, ArithExpr e1, ArithExpr e2) {
        try {
            BoolExpr loBoundExpr1, upBoundExpr1, loBoundExpr2, upBoundExpr2, loUpBoundExpr1, loUpBoundExpr2;
            BoolExpr beTrue = ctx.mkTrue();
            // System.out.println("e1 and e2 "+e1 + " "+e2);
            if (e1.isIntNum() || (e1.isApp() && e1.getNumArgs() == 0 && e1.isInt())) { //var bounds are generated at the end
                loUpBoundExpr1 = beTrue;
            } else {
                loBoundExpr1 = ctx.mkLe((ArithExpr) ctx.mkInt(Util.min_neg()), e1);
                upBoundExpr1 = ctx.mkLe(e1, (ArithExpr) ctx.mkInt(Util.max_pos()));
                loUpBoundExpr1 = ctx.mkAnd(loBoundExpr1, upBoundExpr1);
            }
            if (e2.isIntNum() || (e2.isApp() && e2.getNumArgs() == 0 && e2.isInt())) {
                loUpBoundExpr2 = beTrue;
            } else {
                loBoundExpr2 = ctx.mkLe((ArithExpr) ctx.mkInt(Util.min_neg()), e2);
                upBoundExpr2 = ctx.mkLe(e2, (ArithExpr) ctx.mkInt(Util.max_pos()));
                loUpBoundExpr2 = ctx.mkAnd(loBoundExpr2, upBoundExpr2);
            }
            return ctx.mkAnd(loUpBoundExpr1, loUpBoundExpr2);
        } catch (Exception e) {
            e.printStackTrace();
        }
        return null;
    }

    public BoolExpr genLoBound(Context ctx, ArithExpr arithExpr) {
        try {
            BoolExpr res = ctx.mkLe((ArithExpr) ctx.mkInt(Util.min_neg()), arithExpr);
            return Z3Interface.standariseArithInEq(res, ctx);
        } catch (Exception e) {
            e.printStackTrace();
        }
        return null;
    }

    public BoolExpr genUpBound(Context ctx, ArithExpr arithExpr) {
        try {
            BoolExpr res = ctx.mkLe(arithExpr, (ArithExpr) ctx.mkInt(Util.max_pos()));
            return Z3Interface.standariseArithInEq(res, ctx);
        } catch (Exception e) {
            e.printStackTrace();
        }
        return null;
    }

    public BoolExpr genBounds(Context ctx, ArithExpr arithExpr) {
        try {
            BoolExpr loBoundExpr1, upBoundExpr1, loUpBoundExpr1;
            BoolExpr beTrue = ctx.mkTrue();
            // System.out.println("e1 and e2 "+e1 + " "+e2);
            if (arithExpr.isIntNum() || (arithExpr.isApp() && arithExpr.getNumArgs() == 0 && arithExpr.isInt())) { //var bounds are generated at the end
                loUpBoundExpr1 = beTrue;
            } else {
                loBoundExpr1 = ctx.mkLe((ArithExpr) ctx.mkInt(Util.min_neg()), arithExpr);
                upBoundExpr1 = ctx.mkLe(arithExpr, (ArithExpr) ctx.mkInt(Util.max_pos()));
                loUpBoundExpr1 = ctx.mkAnd(loBoundExpr1, upBoundExpr1);
            }
            return loUpBoundExpr1;
        } catch (Exception e) {
            e.printStackTrace();
        }
        return null;
    }

    /**
     * Graeme's bound
     */
    public void genOptDeltaBound(String id, Context ctx, ArithExpr e, IntExpr delta, GurobiInterface grbInterface, GRBEnv env, Solver deltaSolver) {
        long min, max;
        long minDelta, maxDelta;
        HashSet<IntExpr> vars = Util.collectVars(e);
        max = maxExpr(grbInterface, env, ctx, e);
        min = minExpr(grbInterface, env, ctx, e);
        minDelta = min / Util.modulo_m() - 1; // "/" is an integer division
        maxDelta = max / Util.modulo_m() + 1;
        //System.out.println("min max==================================== " + delta + "  " + minDelta + " " + maxDelta);
        BoolExpr deltaBounds = genDeltaBounds(ctx, delta, ctx.mkInt(minDelta), ctx.mkInt(maxDelta));
        deltaSolver.add(ctx.mkImplies(idStringToBoolExpr.get(id), deltaBounds));
    }

    public BoolExpr genDeltaBounds(Context ctx, IntExpr delta, IntExpr loBound, IntExpr upBound) {
        BoolExpr loBoundDelta, upBoundDelta;
        loBoundDelta = ctx.mkLe(loBound, delta);
        upBoundDelta = ctx.mkLe(delta, upBound);
        return ctx.mkAnd(loBoundDelta, upBoundDelta);
    }

    public long maxExpr(GurobiInterface grbInterface, GRBEnv env, Context ctx, ArithExpr e) {
        GRBModel grbMaxOpt = grbInterface.getGRBModel(env);
        HashSet<IntExpr> z3VarsExpr = Util.collectVars(e);
        HashMap<IntExpr, GRBVar> z3GRBVarMapLocal = Util.getGRBVars(grbMaxOpt, z3VarsExpr);
        grbInterface.updateModel(grbMaxOpt);
        BoolExpr constraints = genVarsBounds(ctx, z3VarsExpr, new HashSet<>());
        grbMaxOpt = new Util().addConstrsGRB(constraints, grbMaxOpt, "dBMax", z3GRBVarMapLocal);
        GRBLinExpr expr = Util.z3Expr2GRBExpr(e, grbMaxOpt, z3GRBVarMapLocal);
        grbInterface.GRBSetMaximize(expr, grbMaxOpt);
        grbInterface.optimize(grbMaxOpt);
        long max = (long) grbInterface.getOptValue(grbMaxOpt);
        grbMaxOpt = null;
        return max;
    }

    public long minExpr(GurobiInterface grbInterface, GRBEnv env, Context ctx, ArithExpr e) {
        GRBModel grbMinOpt = grbInterface.getGRBModel(env);
        HashSet<IntExpr> z3VarsExpr = Util.collectVars(e);
        HashMap<IntExpr, GRBVar> z3GRBVarMapLocal = Util.getGRBVars(grbMinOpt, z3VarsExpr);
        grbInterface.updateModel(grbMinOpt);
        BoolExpr constraints = genVarsBounds(ctx, z3VarsExpr, new HashSet<>());
        grbMinOpt = new Util().addConstrsGRB(constraints, grbMinOpt, "dBMin", z3GRBVarMapLocal);
        GRBLinExpr expr = Util.z3Expr2GRBExpr(e, grbMinOpt, z3GRBVarMapLocal);
        grbInterface.GRBSetMinimize(expr, grbMinOpt);
        grbInterface.optimize(grbMinOpt);
        long min = (long) grbInterface.getOptValue(grbMinOpt);
        grbMinOpt = null;
        return min;
    }

    public ArithExpr genAExprBVNumber(int exprWidth, Context ctx, IntNum e) {
        IntExpr eInt = ctx.mkInt(Util.getModuloM((IntNum) e, exprWidth)); //brings everything under modulo (16 mod 5= 1)
        long num = Long.parseLong(eInt.toString());
        if (num < 0) { //if is a neg nr, return M+e
            num = Util.modulo_m(exprWidth) + num;
            return (ArithExpr) ctx.mkInt(num);
        }
        return eInt;
    }

    public ArithExpr genMAForAExpr(Context ctx, String key, ArithExpr e, GRBModel grbModel, GurobiInterface grbInterface) {//number must have a fixed interpretation
        if (e.isIntNum()) { //z3 treats (- 8) as unary minus not as integer but -8 (without space) is integer in z3 
            return genAExprBVNumber(Main.INT_WIDTH, ctx, (IntNum) e);
        }
        if (e.isApp() && e.getNumArgs() == 0) {
            return e;
        }
        ArithExpr deltaExpr = genDeltaExpr(ctx, key);
        ArithExpr ae = ctx.mkAdd(e, deltaExpr);
        deltaGenerated = true; //to track if the delta expr was generated
        return ae;
    }

    public boolean isArithInEq(Expr e) {
        return (e.isLE() || e.isGE() || e.isGT() || e.isLT() || e.isEq());
    }

    public BoolExpr genMABoolExpr(Context ctx, String key, Expr e, boolean negate, Z3Interface z3Interface, GRBModel gRBModel, GurobiInterface grbInterface, GRBEnv env, Solver deltaSolver) {
        Expr[] andExprs, orExprs;
        BoolExpr beOr = ctx.mkFalse(), beAnd = ctx.mkTrue();
        if (e.isFalse() || e.isTrue()) {
            return (BoolExpr) e;
        }
        if (e.isNot()) {
            return ctx.mkNot(genMABoolExpr(ctx, key, e.getArgs()[0], negate, z3Interface, gRBModel, grbInterface, env, deltaSolver));
        }

        if (e.isOr()) {
            orExprs = e.getArgs();
            if (orExprs.length > 0) {
                beOr = genMABoolExpr(ctx, key, orExprs[0], negate, z3Interface, gRBModel, grbInterface, env, deltaSolver);
            }
            for (int i = 1; i < orExprs.length; i++) {
                beOr = ctx.mkOr(beOr, genMABoolExpr(ctx, key, orExprs[i], negate, z3Interface, gRBModel, grbInterface, env, deltaSolver));
            }
            return beOr;
        }

        if (e.isAnd()) {
            andExprs = e.getArgs();
            if (andExprs.length > 0) {
                beAnd = genMABoolExpr(ctx, key, andExprs[0], negate, z3Interface, gRBModel, grbInterface, env, deltaSolver);
            }
            for (int i = 1; i < andExprs.length; i++) {
                beAnd = ctx.mkOr(beAnd, genMABoolExpr(ctx, key, andExprs[i], negate, z3Interface, gRBModel, grbInterface, env, deltaSolver));
            }
            return beAnd;
        }
        if (isArithInEq(e)) {
            //System.out.println("e " + e);
            return genMAExprArithInEq(ctx, key, e, negate, z3Interface, gRBModel, grbInterface, env, deltaSolver);
        }
        return null;
    }

    public BoolExpr genMAExprArithInEq(Context ctx, String key, Expr e, boolean negate, Z3Interface z3Interface, GRBModel gRBModel, GurobiInterface grbInterface, GRBEnv env, Solver deltaSolver) {
        ArithExpr ae1 = null, ae2 = null;
        deltas = new IntExpr[2];
        BoolExpr be = null;
        if (isArithInEq(e)) {
            Expr[] exprs = e.getArgs();
            ArithExpr aExpr1 = (ArithExpr) exprs[0];
            ae1 = genMAForAExpr(ctx, key, aExpr1, gRBModel, grbInterface);
            if (deltaGenerated) {
                IntExpr delta1 = lastDelta;
                deltas[0] = delta1;
                //genOptDeltaBound(ctx, aExpr1, delta1, z3Interface, grbInterface, env, gRBModel, deltaSolver);
                deltaGenerated = false;
            }
            ArithExpr aExpr2 = (ArithExpr) exprs[1];
            ae2 = genMAForAExpr(ctx, key, aExpr2, gRBModel, grbInterface);
            if (deltaGenerated) {
                IntExpr delta2 = lastDelta;
                deltas[1] = delta2;
                //genOptDeltaBound(ctx, aExpr2, delta2, z3Interface, grbInterface, env, gRBModel, deltaSolver);
                deltaGenerated = false;
            }
        }
        if (e.isFalse() || e.isTrue()) {
            return (BoolExpr) e;
        }
        if (e.isEq()) {
            if (negate) {
                be = ctx.mkNot(ctx.mkEq(ae1, ae2));
            } else {
                be = ctx.mkEq(ae1, ae2);
            }
        } else if (e.isGT()) {
            if (negate) {
                be = ctx.mkLe(ae1, ae2);
            } else {
                be = ctx.mkGt(ae1, ae2);
            }
        } else if (e.isGE()) {
            if (negate) {
                be = ctx.mkLt(ae1, ae2);
            } else {
                be = ctx.mkGe(ae1, ae2);
            }
        } else if (e.isLT()) {
            if (negate) {
                be = ctx.mkGe(ae1, ae2);
            } else {
                be = ctx.mkLt(ae1, ae2);
            }
        } else if (e.isLE()) {
            if (negate) {
                be = ctx.mkGt(ae1, ae2);
            } else {
                be = ctx.mkLe(ae1, ae2);
            }
        } else {
            System.out.println(e + "is not an arithmetic inequality ");
        }
        return be;
    }

    /**
     * (a+b.c-c.d)mod m = a mod m + b.c mod m - c.d mod m. But if this result is
     * negative, which is equivalent to m-result
     */
    public ArithExpr genModuloAExpr(Context ctx, ArithExpr e) {//number must have a fixed interpretation
        IntExpr moduloM = ctx.mkInt(Util.modulo_m());
        IntExpr lowerBound = ctx.mkInt(Util.min_neg());
        IntExpr ae = ctx.mkMod((IntExpr) e, moduloM);
        return (ArithExpr) ctx.mkITE(ctx.mkLt(ae, lowerBound), ctx.mkAdd(moduloM, ae), ae);
    }

    public BoolExpr genModuloArithInEq(Context ctx, Expr e) {
        ArithExpr ae1 = null, ae2 = null;
        BoolExpr be = null;
        IntExpr zero = ctx.mkInt(0);
        IntExpr one = ctx.mkInt(1);
        if (isArithInEq(e)) {
            Expr[] exprs = e.getArgs();
            ae1 = genModuloAExpr(ctx, (ArithExpr) exprs[0]);
            ae2 = genModuloAExpr(ctx, (ArithExpr) exprs[1]);
        }
        if (e.isTrue()) {
            be = ctx.mkLe(zero, zero);
        } else if (e.isFalse()) {
            be = ctx.mkLe(one, zero);
        } else if (e.isEq()) {
            be = ctx.mkEq(ae1, ae2);
        } else if (e.isGT()) {
            be = ctx.mkGt(ae1, ae2);
        } else if (e.isGE()) {
            be = ctx.mkGe(ae1, ae2);
        } else if (e.isLT()) {
            be = ctx.mkLt(ae1, ae2);
        } else if (e.isLE()) {
            be = ctx.mkLe(ae1, ae2);
        } else {
            System.out.println(e + "is not an arithmetic inequality genModuloArithInEq");
        }
        return be;
    }

    public String getIneqSign(String id) {
        BoolExpr formula = transformedFormulas.get(id).getOriginalFormula();
        System.out.println("formula " + formula);
        if (formula.isGE()) {
            return ">=";
        }
        if (formula.isLE()) {
            return "<=";
        }
        return "=";
    }

    public String getIneqSign(BoolExpr formula) {
        if (formula.isGE()) {
            return ">=";
        }
        if (formula.isLE()) {
            return "<=";
        }
        return "=";
    }

    public ArithExpr getDeltaExprCut(IntExpr delta1, IntExpr delta2, String exprSign, Context ctx) {
        if (exprSign.equals(">=")) {
            return ctx.mkSub(delta1, delta2);
        }
        if (exprSign.equals("<=")) {
            return ctx.mkSub(delta2, delta1);
        }
        //equal case
        return ctx.mkSub(delta1, delta2);
    }

    //linear cut but maybe unsound, myway
    public void addLinearCutUnsatCore(Context context, String[] conflicts, Solver deltaSolver, Model previousDeltaModel) {
        BoolExpr cutExpr = context.mkFalse();
        String id;
        int index;
        TransformedFormula tf;
        IntExpr zero = context.mkInt(0);
        ArithExpr acc = context.mkInt(0);
        for (String coreId : conflicts) {
            id = mapIdToOriginal(context, coreId);
            tf = transformedFormulas.get(id);
            index = getConstraintIndex(coreId);
            ArithFormula af = tf.getFormula().get(index);
            acc = context.mkAdd(acc, context.mkSub(af.getDeltaExpr(), (ArithExpr) Z3Interface.evalExprInModel(previousDeltaModel, af.getDeltaExpr())));
        }
        cutExpr = context.mkGt(acc, zero);
//        System.out.println("cut before ==================" + cutExpr);
        cutExpr = (BoolExpr) cutExpr.simplify();
//        System.out.println("cut is ==================" + cutExpr);
        deltaSolver.add(cutExpr);
    }

    /*
     Graeme's way
     */
    public void addCutUnsatCoreGraeme(Context context, String[] conflicts, Solver deltaSolver, Model previousDeltaModel) {
        BoolExpr cutExpr = context.mkFalse();
        String id;
        int index;
        BoolExpr cutSingleConstr;
        BoolExpr coreAssumption = context.mkTrue();
        TransformedFormula tf;
        BoolExpr boolId;
        //IntExpr zero = context.mkInt(0);
        for (String coreId : conflicts) {
//            System.out.println("transformed "+coreId);
            boolId = getIdsBoolExpr(coreId, context);
            coreAssumption = context.mkAnd(coreAssumption, boolId);
            id = mapIdToOriginal(context, coreId);
            tf = transformedFormulas.get(id);
            index = getConstraintIndex(coreId);
            ArithFormula af = tf.getFormula().get(index);
            //System.out.println("core generating "+coreId+" "+af.getFormula());
            if (af.isEquality()) {
                cutSingleConstr = context.mkNot(context.mkEq(af.getDeltaExpr(), Z3Interface.evalExprInModel(previousDeltaModel, af.getDeltaExpr())));
                //cutSingleConstr = context.mkImplies(cutAssumptions, cutSingleConstr);
//                System.out.println("cut is eq==================" + cutSingleConstr);
                //was this before
                //cutExpr = context.mkImplies(cutAssumptions, context.mkOr(cutExpr, cutSingleConstr));
                cutExpr = context.mkOr(cutExpr, cutSingleConstr);

            } else {
                cutSingleConstr = context.mkGt(af.getDeltaExpr(), (ArithExpr) Z3Interface.evalExprInModel(previousDeltaModel, af.getDeltaExpr()));
                //cutSingleConstr = context.mkImplies(cutAssumptions, cutSingleConstr);
//                System.out.println("cut is ==================" + cutSingleConstr);
                //was this before
//                cutExpr = context.mkImplies(cutAssumptions, context.mkOr(cutExpr, cutSingleConstr));
                cutExpr = context.mkOr(cutExpr, cutSingleConstr);
            }
            //System.out.println("cut before single ==================" + cutSingleConstr);
        }
        //System.out.println("cut before ==================" + cutExpr);
        cutExpr = context.mkImplies(coreAssumption, cutExpr);
        cutExpr = (BoolExpr) cutExpr.simplify();
//        System.out.println("cut is ==================" + cutExpr);
        deltaSolver.add(cutExpr);
    }

    public boolean isIdInAssumption(String id, BoolExpr[] assumptions) {
        for (int i = 0; i < assumptions.length; i++) {
            if (id.equals(assumptions[i].toString())) {
                return true;
            }
        }
        return false;
    }

    public ArrayList<String> diffAssumptions(String[] previous, String[] current) {
        ArrayList<String> diffAssumptions = new ArrayList<>();
        HashSet<String> currentSet = new HashSet<String>(Arrays.asList(current));
        for (String s : previous) {
            if (!currentSet.contains(s)) {
                diffAssumptions.add(s);
            }
        }
        return diffAssumptions;
    }

    //note:only  intially unsat core = all constraints
    //transform only those whose delta values have been changed
    public Witness solveTransformedFormula(Z3Interface z3Interface, Context context, GRBEnv env, GurobiInterface grbInterface, Solver disjSolver, GRBModel grbModel, Model disjModel, String[] unsatConstraints) {
        TransformedFormula tf1;
        Util.print(PRINT_FLAG, "solving disjoint");
        Status quotientStatus = z3Interface.checkFormula(disjSolver);
        Util.print(PRINT_FLAG, "finished solved disjoint");
//         System.out.println("delta solver " + disjSolver);

        if (quotientStatus == Status.UNSATISFIABLE) {
//            System.out.println("================================NO quotient possible==================================");
            return new Witness(false, null, unsatConstraints);
//            return null; //all delta coeff are tried, and find a different disjunct, 
        }

        if (deltaValuesModified || refinementCount == 0) { //compute model in the first iteration and when delta is modified
            disjModel = disjSolver.getModel();
        }
//        System.out.println("dis model ============ \n" + disjModel);
        previousAssumptions = currentAssumptions;
        Util.print(PRINT_FLAG, "obtaining current assumption");
        currentAssumptions = getCurrentAssumptionUnder(disjModel, context);
        //System.out.println(Message.printUnsatCore(currentAssumptions));
//        if (isFalseAnyFormula(currentAssumptions)) {
//            //the conjuction of chosen formulas contains false
//            disjSolver.add(context.mkNot(stringListToBF(context, currentAssumptions)));
//            return solveTransformedFormula(z3Interface, context, env, grbInterface, disjSolver, grbModel, disjModel, unsatConstraints);
//        } else {
        if (currentAssumptions.length == 0) {
            System.out.println("================================all assumptions are false==================================");
            return new Witness(false, null, unsatConstraints);
//            return null; //all delta coeff are tried, and find a different disjunct, 
        }
        Util.print(PRINT_FLAG, "obtained current assumption");
        if (refinementCount > 0) {
            ArrayList<String> diffAssumptions = diffAssumptions(previousAssumptions, currentAssumptions);
            //remove constraints pertaining to the previous assumptions
            for (String s : diffAssumptions) {
                //remove constraints
                tf1 = transformedFormulas.get(s);
                int nrConstraints = tf1.getFormulaSize();
                boolean alreadyInSolver = tf1.isAlreadyInTransformedFormInThesolver();
                if (alreadyInSolver) { //delta model will  change and the constraint cannot stay in the solver
                    for (int i = 0; i < nrConstraints; i++) {
                        String idNew = s + "__r__" + i;
                        grbInterface.removeConstraint(grbModel, idNew);
                    }
                }
                tf1.setAlreadyInTransformedFormInThesolver(false);
            }
        }

        //get constraints which are feasible under this disjmodel
        Util.print(PRINT_FLAG, "adding constraints gurobi");
        for (String id : currentAssumptions) {
//            if (isIdInAssumption(id, currentAssumptions)) {
            TransformedFormula tf = transformedFormulas.get(id);
            if (tf.getStatus() == 0) {
                //add the original formula
                if (refinementCount == 0) { //just add once
                    if (!tf.getOriginalFormula().isTrue()) { //true formula is not needed to add
                        // System.out.println("tf.getOriginalFormula() "+tf.getOriginalFormula());
                        grbModel = new Util().addAConstrGRB(tf.getOriginalFormula(), grbModel, id, z3GRBVarMap);
                    }
                }
            } else {
                grbModel = addNextFormulaToSolver(id, grbModel, env, grbInterface, context, z3Interface, disjModel, refinementCount);
            }
        }
        Util.print(PRINT_FLAG, "finished adding constraints");
        Witness mixedLIAWitness = solveMixedLiaFormula(grbModel, context, z3Interface, grbInterface);
        Util.print(PRINT_FLAG, "solved formula gurobi ");
        if (mixedLIAWitness.isSatisfiable()) {
            return mixedLIAWitness;
        } else {
            Util.print(PRINT_FLAG, "refining unsat");
            String[] unsatCore = mixedLIAWitness.getUnsatCore();
            grbModel = refineModel(unsatCore, grbModel, env, grbInterface, context, z3Interface, disjSolver, disjModel, refinementCount);
            refinementCount++;
            if (!deltaValuesModified) { //not a real unsat core, the core  produced from the constraints unsat over Z-model
                //deltaValuesModified is always true, so make this case in a different place
                unsatCore = transformedFormulas.keySet().toArray(new String[transformedFormulas.size()]);
            }
            Util.print(PRINT_FLAG, "refined unsat");
            return solveTransformedFormula(z3Interface, context, env, grbInterface, disjSolver, grbModel, disjModel, unsatCore);
        }
//        }
    }

    public GRBModel addNextFormulaToSolver(String formulaId, GRBModel grbModel, GRBEnv env, GurobiInterface grbInterface, Context context, Z3Interface z3Interface, Model deltaModel, int refinementCount) {
        ArrayList<BoolExpr> simplifiedFormula;
        TransformedFormula tf = transformedFormulas.get(formulaId);
        int nrConstraints = tf.getFormulaSize();
        boolean alreadyInSolver = tf.isAlreadyInTransformedFormInThesolver();
        if (deltaValuesModified && alreadyInSolver) { //delta model will not change and the constraint can stay in the solver
            for (int i = 0; i < nrConstraints; i++) {
                String idNew = formulaId + "__r__" + i;
                grbInterface.removeConstraint(grbModel, idNew);
            }
            simplifiedFormula = selectQuotient(formulaId, context, deltaModel);
            //System.out.println("simplified formula "+simplifiedFormula);
            grbModel = new Util().addListConstrsGRB(simplifiedFormula, grbModel, formulaId, z3GRBVarMap);
            tf.setAlreadyInTransformedFormInThesolver(true);
        } else if (!alreadyInSolver) { //delta model will not change and the constraint can stay in the solver
            simplifiedFormula = selectQuotient(formulaId, context, deltaModel);
            //System.out.println("simplified formula "+tf.getOriginalFormula());
            grbModel = new Util().addListConstrsGRB(simplifiedFormula, grbModel, formulaId, z3GRBVarMap);
            tf.setAlreadyInTransformedFormInThesolver(true);
        }
        simplifiedFormula = null; //releasing memory
        //no change to grbmodel in other cases
        return grbModel;
    }

    public GRBModel refineModel(String[] unsatCore, GRBModel grbModel, GRBEnv env, GurobiInterface grbInterface, Context context, Z3Interface z3Interface, Solver deltaSolver, Model deltaModel, int refinementCount) {
        String[] originalIdsInCore = getOriginalIdsFromCore(unsatCore);
        int length = originalIdsInCore.length;
        if (length > 0) {
            TransformedFormula toTransform;
            String originalId;
            for (int i = 0; i < length; i++) {
                originalId = unsatCore[i];
                toTransform = transformedFormulas.get(originalId);
                grbInterface.removeConstraint(grbModel, originalId); //remove constriants and set status to 1 so that it will get added in the next round
                toTransform = refineTransformedFormula(toTransform, grbModel, context, originalId, z3Interface, grbInterface, env, deltaSolver);
                toTransform.setStatus(1);
                nrConstraintRelaxed++;
            }
            deltaValuesModified = true;
        } else {
            addCutUnsatCoreGraeme(context, unsatCore, deltaSolver, deltaModel);
            deltaValuesModified = true;
        }
        return grbModel; //means, the constraints are added normally
    }

    public String[] getOriginalIdsFromCore(String[] unsatCore) {
        Set<String> originalConstraints = transformedFormulas.keySet();
        ArrayList<String> originalUnsat = new ArrayList<>();
        for (String id : unsatCore) {
            if (originalConstraints.contains(id)) {
                originalUnsat.add(id);
            }
        }
        return originalUnsat.toArray(new String[originalUnsat.size()]);
    }

    /*fix refinement count*/
    public Witness solveDisjointFormula(Z3Interface z3Interface, Context context, GRBEnv env, GurobiInterface grbInterface, Solver disjSolver, Model disjModel, String[] unsatConstraints) {
        GRBModel grbModel = grbInterface.getGRBModel(env);
        z3GRBVarMap = Util.getGRBVars(grbModel, vars);
        grbInterface.updateModel(grbModel); //do update after variable addition
//        System.out.println("disj solver " + disjSolver);
        // System.out.println("checking sat of disj solver");
        Status disjStatus = disjSolver.check();
        //System.out.println("disj solver returned");
        if (disjStatus == Status.UNSATISFIABLE) {
            return new Witness(false, null, unsatConstraints);
        }
        Witness w = solveTransformedFormula(z3Interface, context, env, grbInterface, disjSolver, grbModel, disjModel, unsatConstraints);
        return w;
    }

    public void blockPreviousModel(Context ctx, Solver disjSolver, Model disjModel) {
        BoolExpr acc = ctx.mkTrue();
        BoolExpr beId;
        //check if putting currentAssumptions instead of transformedFormulas.keySet would be fine
        for (String s : transformedFormulas.keySet()) {
            beId = getIdsBoolExpr(s, ctx);
            if (Z3Interface.evalExprInModel(disjModel, beId).isTrue()) {
                acc = ctx.mkAnd(acc, beId);
            } else {
                acc = ctx.mkAnd(acc, ctx.mkNot(beId));
            }
        }
        acc = (BoolExpr) ctx.mkNot(acc).simplify();//put not
        disjSolver.add(acc);
    }

    //highly inefficient
    String[] getCurrentAssumptionUnder(Model m, Context context) {
        BoolExpr assumptionFormula = context.mkTrue();
        ArrayList<String> assumptions = new ArrayList<>();
        Set<String> constrIds = transformedFormulas.keySet();
        BoolExpr boolId;
        for (String s : constrIds) {
            boolId = getIdsBoolExpr(s, context);
//            System.out.println("querying model");
            if (Z3Interface.evalExprInModel(m, boolId).isTrue()) {
//                System.out.println("queried model");
                assumptions.add(s);
//                System.out.println("added assumption");
                assumptionFormula = context.mkAnd(assumptionFormula, boolId);
//                System.out.println("made and formula");
            };
//            System.out.println("query false");
        }
//        System.out.println("simplifying assumption");
        cutAssumptions = assumptionFormula;
        Util.print(PRINT_FLAG, "converting assumptions to array");
        return assumptions.toArray(new String[assumptions.size()]);
    }

    public BoolExpr stringListToBF(Context ctx, String[] liaFormulas) {
        BoolExpr acc = ctx.mkTrue();
        if (liaFormulas.length > 0) {
            acc = getIdsBoolExpr(liaFormulas[0], ctx);
        }
        for (int i = 1; i < liaFormulas.length; i++) {
            acc = ctx.mkAnd(acc, getIdsBoolExpr(liaFormulas[i], ctx));
        }
        return acc;
    }

    public boolean isFalseAnyFormula(String[] ids) {
        for (String s : ids) {
            if (transformedFormulas.get(s).getOriginalFormula().isFalse()) {
                // System.out.println("contains false "+s+" in "+Message.printUnsatCore(currentAssumptions));
                return true;
            }
        }
        return false;
    }

    public Witness decideMaSat(String inputFile) {
//        System.out.println(inputFile);
        try {
            initialize();
            Z3Interface z3Interface = new Z3Interface();
            GurobiInterface grbInterface = new GurobiInterface();
            PreProcessBV ppBV = new PreProcessBV();
            GRBEnv env = grbInterface.createGRBEnv();
            Context context = z3Interface.getContext();
            //get smt-logic
            BoolExpr bExpr = z3Interface.readSMTInput(inputFile, context);
            //process bit-vector formulas
            if (Main.SMT_LOGIC.equals("QF_BV") || Main.SMT_LOGIC.equals("QF_AUFBV") || Main.SMT_LOGIC.equals("BV")) {
                bExpr = (BoolExpr) z3Interface.preProcessQFBVFormulas(context, bExpr).simplify();
                //            Util.print(PRINT_FLAG,"finished pre-processing");
                if (bExpr.isFalse()) {
//                    System.out.println("unsat from preprocessing");
                    return new Witness(false, null, null);
                }
                if (bExpr.isTrue()) {
//                    System.out.println("sat from preprocessing");
                    return new Witness(true, null, null);
                }
                //System.out.println("before nnf  " + bExpr);
                //bExpr = z3Interface.getNNF(context, bExpr);
                //System.out.println("bv expr " + bExpr);
                //translate bit-vector formulas to integer formulas
                bExpr = ppBV.translateToLIA(context, bExpr);
                //System.out.println("pE " + bExpr);
            }
            //System.out.println("lia expr " + bExpr);
            Util.print(PRINT_FLAG, "lia expr: " + bExpr);
            //z3Interface.solveBVTactic(bExpr, context);
            Util.print(PRINT_FLAG, "finished translating to lia");
            //if C1 \/ C2 then introduce id1 ->C1 /\ id2-> C2 /\ (id1 \/id2), the disjSolver does this id selection
            Solver disjSolver = z3Interface.createMinimalModelProdSolver(context);
            //HashMap<String, TransformedFormula> formulas = new HashMap<>();
            //boolIds captures the boolean structure of the formula
            BoolExpr boolStructure = assignIdToFormula(bExpr, context, transformedFormulas, disjSolver);
            Set<String> ids = transformedFormulas.keySet();
//            for (String id
//                    : ids) {
//                Util.print(PRINT_FLAG,"id formula " + id + ": " + transformedFormulas.get(id).getOriginalFormula());
//            }
            Util.print(PRINT_FLAG, "finished identifying");
            disjSolver.add(boolStructure);

            //System.out.println("boo structure " + boolStructure.simplify());
            //            for (String s : formulas.keySet()) {
            //                System.out.println(" " + s + " " + formulas.get(s).getOriginalFormula());
            //            }
            GRBModel grbModel = grbInterface.getGRBModel(env);
            z3GRBVarMap = Util.getGRBVars(grbModel, vars);

            grbInterface.updateModel(grbModel); //do update after variable addition

            Set<String> constraints = transformedFormulas.keySet();
            String[] constraintIds = constraints.toArray(new String[constraints.size()]);
            for (String id : constraintIds) {
                TransformedFormula tf = getTransformedFormula(context, id, z3Interface, grbInterface, env);
                transformedFormulas.put(id, tf);
            }
            Model deltaModel = null;

            Witness maWitness = solveTransformedFormula(z3Interface, context, env, grbInterface, disjSolver, grbModel, deltaModel, constraintIds);
            z3Interface = null;
            return maWitness;

            //return null;
        } catch (Z3Exception ex) {
            System.out.println("Z3 error " + ex.getMessage());
            ex.printStackTrace();
        } catch (Exception e) {
            System.out.println(" Error " + e.getMessage() + inputFile);
            e.printStackTrace();
        }
        return null;
    }

    public Delta[] getDeltaValues(Delta[] deltaParams, Model deltaModel, Context context, Z3Interface z3Interface) {
        Delta[] deltaValues = new Delta[2];
        IntExpr d1, d2;
        if (deltaParams[0] != null) {
            d1 = (IntExpr) z3Interface.evalExprInModel(deltaModel, deltaParams[0].getVar());
            deltaValues[0] = new Delta(deltaParams[0].getVar(), d1);
        } else {
            deltaValues[0] = null;
        }
        if (deltaParams[1] != null) {
            d2 = (IntExpr) z3Interface.evalExprInModel(deltaModel, deltaParams[1].getVar());
            deltaValues[1] = new Delta(deltaParams[1].getVar(), d2);
        } else {
            deltaValues[1] = null;
        }
        return deltaValues;

    }

    public ArrayList<BoolExpr> selectQuotient(String id, Context context, Model deltaModel) {
        ArrayList<BoolExpr> formulasWFixedCoeffs = new ArrayList<>();
        TransformedFormula tf = transformedFormulas.get(id);
        BoolExpr beEval;
        if (tf.getStatus() == 0) { //if it was not transfered, then there is no delta
            beEval = tf.getOriginalFormula();
            formulasWFixedCoeffs.add(beEval);
        } else {
            ArrayList<ArithFormula> arithFormulas = tf.getFormula();
            int length = arithFormulas.size();
            for (int i = 0; i < length; i++) {
                ArithFormula af = arithFormulas.get(i);
//            System.out.println("af ====== " + af.getFormula());
                beEval = (BoolExpr) Z3Interface.evalExprInModelWoMc(deltaModel, af.getFormula());
//            System.out.println("be eval " + beEval);
                formulasWFixedCoeffs.add(beEval);
            }
        }

        return formulasWFixedCoeffs;
    }

    public TransformedFormula getTransformedFormula(Context context, String id, Z3Interface z3Interface, GurobiInterface grbInterface, GRBEnv env) {
        TransformedFormula tf = transformedFormulas.get(id);
        BoolExpr formula = tf.getOriginalFormula();
        tf.setStatus(0); //not yet transformed with deltas or decomposed
        tf.setFormulaWModulo(genModuloArithInEq(context, formula));
        tf.setAlreadyInTransformedFormInThesolver(false); //at the beginning a constrint is not in transformed form in the solver
        return tf;
    }

    //returns null if the formula if false, returns the same TransformedFormula if the formula is true
    public TransformedFormula refineTransformedFormula(TransformedFormula tf, GRBModel grbModel, Context context, String id, Z3Interface z3Interface, GurobiInterface grbInterface, GRBEnv env, Solver deltaSolver) {

        BoolExpr formula = transformedFormulas.get(id).getOriginalFormula();
        if (formula.isTrue()) { //this formula plays no role in the satisfiability
            return tf;
        }
        IntExpr zero = context.mkInt(0);
        IntExpr one = context.mkInt(1);
        ArrayList<ArithFormula> arithFormulas = new ArrayList<>();
        if (formula.isFalse()) { //this just makes model infesible
            BoolExpr exprFalse = context.mkLe(one, zero);
            arithFormulas.add(new ArithFormula(exprFalse, zero, false));
            tf.setFormula(arithFormulas);
            tf.setFormulaSize(1);
            return tf;
        }
        BoolExpr maExpr = genMABoolExpr(context, id, formula, false, z3Interface, grbModel, grbInterface, env, deltaSolver);
        BoolExpr moduloExpr = genVarsBounds(context, Util.collectVars(formula), new HashSet<>()); //this will have all the constraints
        BoolExpr preProcessedExpr;
        String inEqSign = getIneqSign(maExpr);
        boolean isEq = maExpr.isEq();
        BoolExpr simplifiedAaExpr = Z3Interface.standariseArithInEq(maExpr, context);
        BoolExpr beLo0 = null;
        BoolExpr beUp0 = null;
        BoolExpr beLo1 = null;
        BoolExpr beUp1 = null;
//        System.out.println(" ma expr ===================== " + maExpr);
        Expr[] exprs = maExpr.getArgs();
        ArithExpr deltaExpr;

        if (deltas[0] != null && deltas[1] != null) {
            deltaExpr = getDeltaExprCut(deltas[0], deltas[1], inEqSign, context);
            arithFormulas.add(new ArithFormula(simplifiedAaExpr, deltaExpr, isEq));
            beLo0 = genLoBound(context, (ArithExpr) exprs[0]);
            arithFormulas.add(new ArithFormula(beLo0, deltas[0], false));
            beUp0 = genUpBound(context, (ArithExpr) exprs[0]);
            arithFormulas.add(new ArithFormula(beUp0, context.mkUnaryMinus(deltas[0]), false));

            beLo1 = genLoBound(context, (ArithExpr) exprs[1]);
            arithFormulas.add(new ArithFormula(beLo1, deltas[1], false));
            beUp1 = genUpBound(context, (ArithExpr) exprs[1]);
            arithFormulas.add(new ArithFormula(beUp1, context.mkUnaryMinus(deltas[1]), false));

            moduloExpr = (BoolExpr) context.mkAnd(maExpr, beLo0, beUp0, beLo1, beUp1, moduloExpr).simplify();
            preProcessedExpr = z3Interface.preProcessArithFormula(context, moduloExpr);
//            System.out.println("preprocessed expr ================= "+ preProcessedExpr);
            if (preProcessedExpr.isFalse()) {
//                System.out.println("is false both deltas");
                Expr[] origExprs = tf.getOriginalFormula().getArgs();
                genOptDeltaBound(id, context, (ArithExpr) origExprs[0], deltas[0], grbInterface, env, deltaSolver);
                genOptDeltaBound(id, context, (ArithExpr) origExprs[0], deltas[1], grbInterface, env, deltaSolver);
            } else {
//                 System.out.println("preproc expr  "+preProcessedExpr.isTrue());
                deltaSolver.add(context.mkImplies(idStringToBoolExpr.get(id), z3Interface.getMaxMinDeltaExpr(context, deltas[0], preProcessedExpr)));
                deltaSolver.add(context.mkImplies(idStringToBoolExpr.get(id), z3Interface.getMaxMinDeltaExpr(context, deltas[1], preProcessedExpr)));
            }

            tf.setFormula(arithFormulas);
            tf.setFormulaSize(5);
            return tf;
        }

        if (deltas[0] != null) {
            deltaExpr = getDeltaExprCut(deltas[0], zero, inEqSign, context);
            arithFormulas.add(new ArithFormula(simplifiedAaExpr, deltaExpr, isEq));
            beLo0 = genLoBound(context, (ArithExpr) exprs[0]);
            arithFormulas.add(new ArithFormula(beLo0, deltas[0], false));
            beUp0 = genUpBound(context, (ArithExpr) exprs[0]);
            arithFormulas.add(new ArithFormula(beUp0, context.mkUnaryMinus(deltas[0]), false));

            moduloExpr = (BoolExpr) context.mkAnd(maExpr, beLo0, beUp0, moduloExpr).simplify();
            preProcessedExpr = z3Interface.preProcessArithFormula(context, moduloExpr);
//            System.out.println("preprocessed expr ================= " + preProcessedExpr);

            if (preProcessedExpr.isFalse()) {
//                System.out.println("is false 0 deltas");
                Expr[] origExprs = tf.getOriginalFormula().getArgs();
                genOptDeltaBound(id, context, (ArithExpr) origExprs[0], deltas[0], grbInterface, env, deltaSolver);
            } else {
//                 System.out.println("preproc expr  "+preProcessedExpr.isTrue());
                deltaSolver.add(context.mkImplies(idStringToBoolExpr.get(id), z3Interface.getMaxMinDeltaExpr(context, deltas[0], preProcessedExpr)));
            }
            tf.setFormula(arithFormulas);
            tf.setFormulaSize(3);
            return tf;
        }

        if (deltas[1] != null) {
            deltaExpr = getDeltaExprCut(zero, deltas[1], inEqSign, context);
            arithFormulas.add(new ArithFormula(simplifiedAaExpr, deltaExpr, isEq));
            beLo1 = genLoBound(context, (ArithExpr) exprs[1]);
            arithFormulas.add(new ArithFormula(beLo1, deltas[1], false));
            beUp1 = genUpBound(context, (ArithExpr) exprs[1]);
            arithFormulas.add(new ArithFormula(beUp1, context.mkUnaryMinus(deltas[1]), false));

            moduloExpr = (BoolExpr) context.mkAnd(maExpr, beLo1, beUp1, moduloExpr).simplify();
            preProcessedExpr = z3Interface.preProcessArithFormula(context, moduloExpr);
//             System.out.println("preprocessed expr ================= "+ preProcessedExpr);
            if (preProcessedExpr.isFalse()) {
//                System.out.println("is false 1 deltas");
                Expr[] origExprs = tf.getOriginalFormula().getArgs();
                genOptDeltaBound(id, context, (ArithExpr) origExprs[1], deltas[1], grbInterface, env, deltaSolver);
            } else {
//                System.out.println("preproc expr  "+preProcessedExpr.isTrue());
                deltaSolver.add(context.mkImplies(idStringToBoolExpr.get(id), z3Interface.getMaxMinDeltaExpr(context, deltas[1], preProcessedExpr)));
            }
            tf.setFormula(arithFormulas);
            tf.setFormulaSize(3);
            return tf;
        }
        // in this case, both deltas are null
        arithFormulas.add(new ArithFormula(simplifiedAaExpr, zero, isEq));
        tf.setFormula(arithFormulas);
        tf.setFormulaSize(1);
        return tf;
    }

    public void setVarBound(long lower, long upper, GRBModel model, String varName) {
        try {
            GRBVar grbVar = model.getVarByName(varName);
            grbVar.set(GRB.DoubleAttr.LB, (double) lower);
            grbVar.set(GRB.DoubleAttr.UB, (double) upper);
        } catch (GRBException e) {
            e.printStackTrace();
        }
    }

    public void setVariablesBound(GRBModel model, HashMap<IntExpr, GRBVar> z3GRBVarMap) {
        try {
            for (IntExpr ie : z3GRBVarMap.keySet()) {
                if (!boundedVars.contains(ie)) {
                    setVarBound(Util.min_neg(), Util.max_pos(), model, ie.getSExpr());
                    boundedVars.add(ie);
                }
            }
        } catch (Exception e) {
            e.printStackTrace();
        }
    }

    public String mapIdToOriginal(Context ctx, String coreId) {
        //String[] result = new String[core.length];
        String suffix = "__r";
        String prefix = coreId;
        if (coreId.contains(suffix)) {//meaning the constraint was relaxed
            prefix = coreId.substring(0, coreId.indexOf(suffix)); //check this
        }
        return prefix;
    }

    public int getConstraintIndex(String coreId) {
        //String[] result = new String[core.length];
        String prefix = "__r__";
        String suffix = coreId.substring(coreId.indexOf(prefix) + 5); //check this
        return Integer.parseInt(suffix);
    }

    public String[] mapUnsatCoreIdsToOriginal(Context ctx, String[] core) {
        HashSet<String> resultH = new HashSet<>();
        for (int i = 0; i < core.length; i++) {
            String s = core[i];
            resultH.add(mapIdToOriginal(ctx, s));
        }
        String[] res = resultH.toArray(new String[resultH.size()]);
        resultH = null;
        return res;
    }

    public void addSoftConstraint(Context ctx, Solver solver, BoolExpr formula, BoolExpr conflictId) {
        String id = conflictId.getSExpr();
        BoolExpr newId = ctx.mkBoolConst(id + "_r");
        //logger.debug("refined formula: \n" + newId + ": " + formula);
        solver.add(ctx.mkImplies(newId, formula));
    }

    public BoolExpr[] replaceAssumption(BoolExpr[] assumptions, BoolExpr source, BoolExpr destination) {
        if (assumptions == null || (assumptions != null && assumptions.length == 0)) {
            return null;
        } else {
            int i = 0;
            while (i < assumptions.length) {
                //System.out.println("assumption= " + assumptions[i] + " souce= "+source);
                if (assumptions[i].equals(source)) {
                    assumptions[i] = destination;
                    return assumptions;
                }
                i++;
            }
            return assumptions;
        }
    }

    /* put the structure of the bool operations in disjSolver, list the rest of the formulas
     return type can be any boolean combination of ids, this method is tuned for modulo arithmetic
     */
    public BoolExpr assignIdToFormula(BoolExpr bExpr, Context ctx, HashMap<String, TransformedFormula> formulas, Solver disjSolver) {
        BoolExpr beId;
        BoolExpr andExpr = ctx.mkTrue();
        BoolExpr orExpr = ctx.mkFalse();
        Expr[] exprs;
        Expr auxBExpr;
        if (bExpr.isFalse()) {
            String id = "fmla_" + formulaCount;
            BoolExpr idBe = getIdsBoolExpr(id, ctx); //for disjoint solver
            disjSolver.add(ctx.mkImplies(idBe, ctx.mkFalse())); //so that it never comes in the model
            formulaCount++;
            formulas.put(id, new TransformedFormula(bExpr, 0, new HashSet<IntExpr>() {
            }));
            return idBe;
//            return ctx.mkImplies(idBe, bExpr); //avoiding this to appear in the boolean model
        }
        if (bExpr.isTrue()) { //do not add, it is already satisfied
            String id = "fmla_" + formulaCount;
            BoolExpr idBe = getIdsBoolExpr(id, ctx); //for disjoint solver
            formulaCount++;
            formulas.put(id, new TransformedFormula(bExpr, 0, new HashSet<IntExpr>() {
            }));
            return idBe;
        }
        if (bExpr.isNot()) { //assuming NNF
            auxBExpr = bExpr.getArgs()[0];
            return assignIdToNegatedFormula((BoolExpr) auxBExpr, ctx, formulas, disjSolver);
        }
        if (bExpr.isAnd()) {
            //beId = assignIdToAtomicFormula(ctx, bExpr, formulas, false);
            //disjSolver.add(beId);
            exprs = bExpr.getArgs();
            for (Expr e : exprs) {
                //BoolExpr beIdAnd = assignIdToAtomicFormula(ctx, (BoolExpr) e, formulas, false);
                //andExpr = ctx.mkAnd(andExpr, beIdAnd);
                beId = assignIdToFormula((BoolExpr) e, ctx, formulas, disjSolver);
                andExpr = ctx.mkAnd(andExpr, beId);
            }
            return andExpr;
        }
        if (bExpr.isOr()) {
            //beId = assignIdToAtomicFormula(ctx, bExpr, formulas, false);
            //disjSolver.add(beId);
            exprs = bExpr.getArgs();
            for (Expr e : exprs) {
                //BoolExpr beIdOr = assignIdToAtomicFormula(ctx, (BoolExpr) e, formulas, false);
                //andExpr = ctx.mkOr(orExpr, beIdOr);
                beId = assignIdToFormula((BoolExpr) e, ctx, formulas, disjSolver);
                orExpr = ctx.mkOr(orExpr, beId);
            }
            //disjSolver.add(ctx.mkEq(beId, orExpr));
            //disjSolver.add(orExpr);
            return orExpr;
        }
        if (isArithInEq(bExpr)) {
            beId = assignIdToAtomicFormula(ctx, bExpr, formulas, true, disjSolver);
            //disjSolver.add(beId);
            return beId;
        }
        if (bExpr.isConst()) {
            //bExpr is a boolean variable
            beId = assignIdToAtomicFormula(ctx, bExpr, formulas, true, disjSolver);
            //disjSolver.add(beId);
            return beId;
        }
        System.out.println("Formula " + bExpr + " not recognized");
        return null;
    }

    //the formula auxBExpr is in NNF
    public BoolExpr assignIdToNegatedFormula(BoolExpr auxBExpr, Context ctx, HashMap<String, TransformedFormula> formulas, Solver disjSolver) {
        Expr[] auxExprs, arthiExprs;
        BoolExpr beId;
        if (auxBExpr.isFalse()) {//do nothing
            Util.print(PRINT_FLAG, "false not  is the case=====");
            String id = "fmla_" + formulaCount;
            BoolExpr idBe = getIdsBoolExpr(id, ctx); //for disjoint solver
            formulaCount++;
            formulas.put(id, new TransformedFormula(ctx.mkTrue(), 0, new HashSet<IntExpr>() {
            }));
            return idBe;
        }
        if (auxBExpr.isTrue()) {
            Util.print(PRINT_FLAG, "true not is the case ====");
            String id = "fmla_" + formulaCount;
            BoolExpr idBe = getIdsBoolExpr(id, ctx); //for disjoint solver
            disjSolver.add(ctx.mkImplies(idBe, ctx.mkFalse()));
            formulaCount++;
            formulas.put(id, new TransformedFormula(ctx.mkFalse(), 0, new HashSet<IntExpr>() {
            }));
            return idBe;
//                return ctx.mkImplies(idBe, (BoolExpr) ctx.mkFalse()); //avoiding this to appear in the boolean model
        }
        if (auxBExpr.isConst()) { //is a boolean variable
            beId = assignIdToAtomicFormula(ctx, auxBExpr, formulas, true, disjSolver);
            return ctx.mkNot(beId);
        }
        if (auxBExpr.isEq()) { //this could well be boolean equality, assume arithmetic for now
            auxExprs = auxBExpr.getArgs();
            beId = assignIdToFormula(ctx.mkOr(ctx.mkGt((ArithExpr) auxExprs[0], (ArithExpr) auxExprs[1]), ctx.mkLt((ArithExpr) auxExprs[0], (ArithExpr) auxExprs[1])), ctx, formulas, disjSolver);
            return beId;
        }
        if (isArithInEq(auxBExpr)) {
            //can be <, <=, >, >=
            arthiExprs = auxBExpr.getArgs();
            ArithExpr a0 = (ArithExpr) arthiExprs[0];
            ArithExpr a1 = (ArithExpr) arthiExprs[1];
            BoolExpr retExpr;
            if (auxBExpr.isLT()) {
                retExpr = ctx.mkGe(a0, a1);
                beId = assignIdToAtomicFormula(ctx, retExpr, formulas, true, disjSolver);
                return beId;
            }
            if (auxBExpr.isLE()) {
                retExpr = ctx.mkGt(a0, a1);
                beId = assignIdToAtomicFormula(ctx, retExpr, formulas, true, disjSolver);
                return beId;
            }
            if (auxBExpr.isGT()) {
                retExpr = ctx.mkLe(a0, a1);
                beId = assignIdToAtomicFormula(ctx, retExpr, formulas, true, disjSolver);
                return beId;
            }
            if (auxBExpr.isGE()) {
                retExpr = ctx.mkLt(a0, a1);
                beId = assignIdToAtomicFormula(ctx, retExpr, formulas, true, disjSolver);
                return beId;
            }
        }

        System.out.println("formula " + auxBExpr + " not recognized");
        return null;

    }

    // tuned for modulo arithmetic
    public BoolExpr assignIdToAtomicFormula(Context ctx, BoolExpr be, HashMap<String, TransformedFormula> formulas, boolean isAtomic, Solver disjSolver) {
        //check for strict inequalities
        if (be.isLT()) {
            Expr[] ineqExprs = be.getArgs();
            BoolExpr retExpr1 = ctx.mkGe((ArithExpr) ineqExprs[1], ctx.mkInt(Util.min_neg() + 1));
            BoolExpr retExpr2 = ctx.mkLe((ArithExpr) ineqExprs[0], ctx.mkSub((ArithExpr) ineqExprs[1], ctx.mkInt(1)));
            BoolExpr retExpr = ctx.mkAnd(retExpr1, retExpr2);
            return assignIdToFormula(retExpr, ctx, formulas, disjSolver);
        }
        if (be.isGT()) {
            Expr[] ineqExprs = be.getArgs();
            BoolExpr retExpr1 = ctx.mkGe((ArithExpr) ineqExprs[0], ctx.mkInt(Util.min_neg() + 1));
            BoolExpr retExpr2 = ctx.mkGe(ctx.mkSub((ArithExpr) ineqExprs[0], ctx.mkInt(1)), (ArithExpr) ineqExprs[1]);
            BoolExpr retExpr = ctx.mkAnd(retExpr1, retExpr2);
            return assignIdToFormula(retExpr, ctx, formulas, disjSolver);
        }
        String id = "fmla_" + formulaCount;
        BoolExpr idBe = getIdsBoolExpr(id, ctx); //for disjoint solver
        formulaCount++;
        HashSet<IntExpr> varsFormula = Util.collectVars(be);
        vars = Util.varUnion(vars, varsFormula);
        formulas.put(id, new TransformedFormula(be, 0, varsFormula));
        return idBe;

    }

    public HashMap<String, TransformedFormula> assignIdToFormula(BoolExpr bExpr, Context ctx, Solver disjSolver) {
        bExpr = (BoolExpr) bExpr;
        ArrayList<Expr> list = new ArrayList<>();
        listConstraints(bExpr, ctx, list);
        Expr[] exprs = list.toArray(new Expr[list.size()]);

        HashMap<String, TransformedFormula> formulas = new HashMap<>();
        boolean isDisjunction = false;
        BoolExpr disjExpr = (BoolExpr) hashFormulas(exprs, ctx, formulas, isDisjunction).simplify();
        //System.out.println("disj expr " + disjExpr);
        disjSolver.add(disjExpr);
        return formulas;
    }

    public BoolExpr hashFormulas(Expr[] exprs, Context ctx, HashMap<String, TransformedFormula> formulas, boolean isDisjunction) {
        BoolExpr be;
        BoolExpr beAnd = ctx.mkTrue();
        for (int i = 0; i < exprs.length; i++) {
            be = (BoolExpr) exprs[i];
            if (be.isOr()) { //single OR nesting considered
                beAnd = ctx.mkAnd(beAnd, hashFormulasSingleList(be.getArgs(), ctx, formulas, true));
            } else {
                beAnd = ctx.mkAnd(beAnd, assignIdToSingleConstraint(be, ctx, formulas));
            }
        }
        return beAnd;
    }

    public BoolExpr hashFormulasSingleList(Expr[] exprs, Context ctx, HashMap<String, TransformedFormula> formulas, boolean isDisjunction) {
        BoolExpr be;
        if (isDisjunction) {
            BoolExpr beOr = ctx.mkFalse();
            for (int i = 0; i < exprs.length; i++) {
                be = (BoolExpr) exprs[i];
                beOr = ctx.mkOr(beOr, assignIdToSingleConstraint(be, ctx, formulas));
            }
            return beOr;
        } else {
            BoolExpr beAnd = ctx.mkTrue();
            for (int i = 0; i < exprs.length; i++) {
                be = (BoolExpr) exprs[i];
                beAnd = ctx.mkAnd(beAnd, assignIdToSingleConstraint(be, ctx, formulas));
            }
            return beAnd;
        }
    }

    public BoolExpr getIdsBoolExpr(String id, Context ctx) {
        BoolExpr idBoolExpr;
        if (idStringToBoolExpr.containsKey(id)) {
            return idStringToBoolExpr.get(id);
        } else {
            idBoolExpr = ctx.mkBoolConst(id);
            idStringToBoolExpr.put(id, idBoolExpr);
            return idBoolExpr;
        }
    }

    public BoolExpr assignIdToSingleConstraint(BoolExpr be, Context ctx, HashMap<String, TransformedFormula> formulas) {
        String id;
        if (be.isNot()) { //assuming negation normal form
            return processNegation(ctx, (BoolExpr) be.getArgs()[0], formulas);
        } else if (be.isLT() || be.isGT()) {
            return convertStrictIneqToNonStrictIneq(ctx, be, formulas);
//            } else if (be.isEq()) {
//                processEqualities(ctx, be, formulas);
        } else {
            id = "fmla_" + formulaCount;
            formulaCount++;
            HashSet<IntExpr> varsFormula = Util.collectVars(be);
            vars = Util.varUnion(vars, varsFormula);
            formulas.put(id, new TransformedFormula(be, 0, varsFormula));
            return getIdsBoolExpr(id, ctx);
        }
    }

    public BoolExpr processNegation(Context ctx, BoolExpr be, HashMap<String, TransformedFormula> formulas) {
        Expr[] exprs = be.getArgs();
        ArithExpr a0 = (ArithExpr) exprs[0];
        ArithExpr a1 = (ArithExpr) exprs[1];
        HashSet<IntExpr> varsFormula;
        BoolExpr retExpr;
        String id;
        if (be.isLE()) {
            retExpr = ctx.mkGt(a0, a1);
            return convertStrictIneqToNonStrictIneq(ctx, retExpr, formulas);
        } else if (be.isLT()) {
            retExpr = ctx.mkGe(a0, a1);
            id = "fmla_" + formulaCount;
            formulaCount++;
            varsFormula = Util.collectVars(retExpr);
            vars = Util.varUnion(vars, varsFormula);
            formulas.put(id, new TransformedFormula(retExpr, 0, varsFormula));
            return getIdsBoolExpr(id, ctx);
        } else if (be.isGE()) {
            retExpr = ctx.mkLt(a0, a1);
            return convertStrictIneqToNonStrictIneq(ctx, retExpr, formulas);
        } else if (be.isGT()) {
            retExpr = ctx.mkLe(a0, a1);
            id = "fmla_" + formulaCount;
            formulaCount++;
            varsFormula = Util.collectVars(retExpr);
            vars = Util.varUnion(vars, varsFormula);
            formulas.put(id, new TransformedFormula(retExpr, 0, varsFormula));
            return getIdsBoolExpr(id, ctx);
        } else {
            //equality could come in
            System.err.println("is a disjunction (not " + be + ")/n not is NNF");
            System.exit(1);
            return null;
        }

    }

    public void listConstraints(BoolExpr bExpr, Context ctx, ArrayList<Expr> exprList) {
        Expr[] exprs1;
        //  ArrayList<Expr> exprList = new ArrayList<>();
        //BoolExpr acc = ctx.mkTrue();
//        System.out.println("bExpr "+bExpr);
        if (!bExpr.isTrue()) {
            if (bExpr.isAnd()) {
                //check if there is a nested and
                exprs1 = bExpr.getArgs();
//            System.out.println("length "+exprs1.length);
                for (int i = 0; i < exprs1.length; i++) {
//                System.out.println("calling collect constraints");
                    listConstraints((BoolExpr) exprs1[i], ctx, exprList);
                }
            } else {
                exprList.add(bExpr);
            }
        }

    }

    /*
     simplify exprssions in each side of the inequalities
     */
    public BoolExpr simplifyArithFormula(Context ctx, BoolExpr be) {
        Expr[] exprs = be.getArgs();
        ArithExpr ae0 = (ArithExpr) exprs[0].simplify();
        ArithExpr ae1 = (ArithExpr) exprs[1].simplify();
        if (be.isLE()) {
            return ctx.mkLe(ae0, ae1);
        }
        if (be.isLT()) {
            return ctx.mkLt(ae0, ae1);
        }
        if (be.isEq()) {
            return ctx.mkEq(ae0, ae1);
        }
        if (be.isGE()) {
            return ctx.mkGe(ae0, ae1);
        }
        if (be.isGT()) {
            return ctx.mkGt(ae0, ae1);
        }
        return null;
    }

    public void processEqualities(Context ctx, BoolExpr be, HashMap<String, TransformedFormula> formulas) {
        Expr[] eqExprs;
        HashSet<IntExpr> varsFormula;
        BoolExpr normalizedExpr;
        String id;
        eqExprs = be.getArgs();

        id = "fmla_" + formulaCount;
        formulaCount++;
        varsFormula = Util.collectVars(be);
        vars = Util.varUnion(vars, varsFormula);

        normalizedExpr = ctx.mkGe((ArithExpr) eqExprs[0], (ArithExpr) eqExprs[1]);
        formulas.put(id, new TransformedFormula(normalizedExpr, 0, varsFormula));

        id = "fmla_" + formulaCount;
        formulaCount++;
        normalizedExpr = ctx.mkLe((ArithExpr) eqExprs[0], (ArithExpr) eqExprs[1]);
        formulas.put(id, new TransformedFormula(normalizedExpr, 0, varsFormula));
    }

    /*
     This convertion holds only for modular arithmetic
     */
    public BoolExpr convertStrictIneqToNonStrictIneq(Context ctx, BoolExpr be, HashMap<String, TransformedFormula> formulas) {
        Expr[] ineqExprs;
        HashSet<IntExpr> varsFormula;
        BoolExpr normalizedExpr;
        String id;
        BoolExpr id1, id2;
        ineqExprs = be.getArgs();
        if (be.isLT()) {
            id = "fmla_" + formulaCount;
            id1 = getIdsBoolExpr(id, ctx);
            formulaCount++;
            normalizedExpr = ctx.mkGe((ArithExpr) ineqExprs[1], ctx.mkInt(Util.min_neg() + 1));
            varsFormula = Util.collectVars(normalizedExpr);
            vars = Util.varUnion(vars, varsFormula);
            formulas.put(id, new TransformedFormula(normalizedExpr, 0, varsFormula));

            id = "fmla_" + formulaCount;
            id2 = getIdsBoolExpr(id, ctx);
            formulaCount++;
            ArithExpr secondExpr = ctx.mkSub((ArithExpr) ineqExprs[1], ctx.mkInt(1));
            normalizedExpr = ctx.mkLe((ArithExpr) ineqExprs[0], secondExpr);
            varsFormula = Util.collectVars(normalizedExpr);
            vars = Util.varUnion(vars, varsFormula);
            formulas.put(id, new TransformedFormula(normalizedExpr, 0, varsFormula));
            return ctx.mkAnd(id1, id2);
        } else if (be.isGT()) {
            id = "fmla_" + formulaCount;
            id1 = getIdsBoolExpr(id, ctx);
            formulaCount++;
            normalizedExpr = ctx.mkGe((ArithExpr) ineqExprs[0], ctx.mkInt(Util.min_neg() + 1));
            varsFormula = Util.collectVars(normalizedExpr);
            vars = Util.varUnion(vars, varsFormula);
            formulas.put(id, new TransformedFormula(normalizedExpr, 0, varsFormula));
            id = "fmla_" + formulaCount;
            id2 = getIdsBoolExpr(id, ctx);
            formulaCount++;
            ArithExpr firstExpr = ctx.mkSub((ArithExpr) ineqExprs[0], ctx.mkInt(1));
            normalizedExpr = ctx.mkGe(firstExpr, (ArithExpr) ineqExprs[1]);
            varsFormula = Util.collectVars(normalizedExpr);
            vars = Util.varUnion(vars, varsFormula);
            formulas.put(id, new TransformedFormula(normalizedExpr, 0, varsFormula));
            return ctx.mkAnd(id1, id2);
        } else {
            return null;
        }
    }

    public boolean allTransformed() {
        for (String b : transformedFormulas.keySet()) {
            if (transformedFormulas.get(b).getStatus() == 0) {
                return false;
            }
        }
        return true;
    }

    public Witness checkMASat(String file, FileWriter log) {
        Witness w = null;
        try {
            initialize();
            long beingTime = System.nanoTime();
            w = decideMaSat(file);
            long endTime = System.nanoTime();
            long time = endTime - beingTime;
            log.write(Message.showStatistics(file, w, time / 1000000, transformedFormulas.size(), refinementCount, nrConstraintRelaxed, false));
            dispose();
        } catch (Exception e) {
            e.printStackTrace();
        }
        return w;
    }

    public Witness checkMASat(String file) {
        Witness w = null;
        try {
            initialize();
            long beingTime = System.nanoTime();
            w = decideMaSat(file);
            long endTime = System.nanoTime();
            long time = endTime - beingTime;
            System.out.println(Message.showStatistics(file, w, time / 1000000, transformedFormulas.size(), refinementCount, nrConstraintRelaxed, false));
            dispose();

        } catch (Exception e) {
            e.printStackTrace();
        }
        return w;
    }

}
