(set-logic QF_BV) 
 
(declare-fun A () (_ BitVec 4)) 
(declare-fun B () (_ BitVec 4)) 
(declare-fun C () (_ BitVec 4)) 
(declare-fun D () (_ BitVec 4)) 
(declare-fun E () (_ BitVec 4)) 
 
(assert 
  (let ((a!1 (bvadd  (bvsub #x0 A)
                    (bvsub  #x0 (bvmul #x2 B))))
        (a!2 (bvadd  A
                    (bvmul #x2 B)
                    (bvsub #x0  D)))
        )
    (and 
         (bvuge a!1 #x6)
         (bvuge C #x1)
         (= a!2 (bvsub #x0 #x1))
)))
(check-sat)