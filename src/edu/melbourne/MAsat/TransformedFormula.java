/*
 * To change this license header, choose License Headers in Project Properties.
 * To change this template file, choose Tools | Templates
 * and open the template in the editor.
 */
package edu.melbourne.MAsat;

import com.microsoft.z3.BoolExpr;
import com.microsoft.z3.IntExpr;
import java.util.ArrayList;
import java.util.HashSet;

/**
 *
 * @author kafle
 */
public class TransformedFormula {

    BoolExpr originalFormula;
    BoolExpr formulaWModulo; //needed for checking sat in a model
    int status; //0 =not trasformed, 1=transformed
    ArrayList<ArithFormula> formula;
    int formulaSize;
    HashSet<IntExpr> vars;
    boolean alreadyInTransformedFormInThesolver; //is already in a transformed form in the solver

    public TransformedFormula() {
    }

    public TransformedFormula(ArrayList<ArithFormula> formula, int formulaSize) {
        this.formula = formula;
        this.formulaSize = formulaSize;
    }

    public int getFormulaSize() {
        return formulaSize;
    }

    public void setFormulaSize(int formulaSize) {
        this.formulaSize = formulaSize;
    }

    public ArrayList<ArithFormula> getFormula() {
        return formula;
    }

    public void setFormula(ArrayList<ArithFormula> formula) {
        this.formula = formula;
    }

    public TransformedFormula(BoolExpr originalFormula, int status, ArrayList<ArithFormula> formula, int formulaSize) {
        this.originalFormula = originalFormula;
        this.status = status;
        this.formula = formula;
        this.formulaSize = formulaSize;
    }

    public BoolExpr getOriginalFormula() {
        return originalFormula;
    }

    public void setOriginalFormula(BoolExpr originalFormula) {
        this.originalFormula = originalFormula;
    }

    public int getStatus() {
        return status;
    }

    public void setStatus(int status) {
        this.status = status;
    }

    public BoolExpr getFormulaWModulo() {
        return formulaWModulo;
    }

    public void setFormulaWModulo(BoolExpr formulaWModulo) {
        this.formulaWModulo = formulaWModulo;
    }

    public TransformedFormula(BoolExpr originalFormula) {
        this.originalFormula = originalFormula;
    }

    public TransformedFormula(BoolExpr originalFormula, int status) {
        this.originalFormula = originalFormula;
        this.status = status;
    }

    public TransformedFormula(BoolExpr originalFormula, BoolExpr formulaWModulo, int status) {
        this.originalFormula = originalFormula;
        this.formulaWModulo = formulaWModulo;
        this.status = status;
    }

    public HashSet<IntExpr> getVars() {
        return vars;
    }

    public void setVars(HashSet<IntExpr> vars) {
        this.vars = vars;
    }

    public TransformedFormula(BoolExpr originalFormula, int status, HashSet<IntExpr> vars) {
        this.originalFormula = originalFormula;
        this.status = status;
        this.vars = vars;
    }

    public boolean isAlreadyInTransformedFormInThesolver() {
        return alreadyInTransformedFormInThesolver;
    }

    public void setAlreadyInTransformedFormInThesolver(boolean alreadyInTransformedFormInThesolver) {
        this.alreadyInTransformedFormInThesolver = alreadyInTransformedFormInThesolver;
    }


}
