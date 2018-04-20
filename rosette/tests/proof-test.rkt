#lang rosette 
 
(require "../cosette.rkt" "../util.rkt" "../denotation.rkt" "../equal.rkt"
         "../table.rkt" "../sql.rkt" "../evaluator.rkt" "../syntax.rkt" "../symmetry.rkt") 
  
(current-bitwidth #f)
 
(define-symbolic div_ (~> integer? integer? integer?))
 
(define t-info (table-info "t" (list "k0" "c1" "f1_a0" "f2_a0" "f0_c0" "f1_c0" "f0_c1" "f1_c2" "f2_c3")))
 
(define account-info (table-info "account" (list "acctno" "type" "balance")))
 
(define bonus-info (table-info "bonus" (list "ename" "job" "sal" "comm")))
 
(define dept-info (table-info "dept" (list "deptno" "name")))
 
(define emp-info (table-info "emp" (list "empno" "ename" "job" "mgr" "hiredate" "comm" "sal" "deptno" "slacker")))
 

(define (q1 tables) 
  (SELECT (VALS "dept.name") 
 FROM (AS (NAMED (list-ref tables 3)) ["dept"]) 
 WHERE (BINOP "dept.name" > 1) GROUP-BY (list "dept.name") 
 HAVING (AND (BINOP "dept.name" > 2) (OR (BINOP (VAL-UNOP aggr-count (val-column-ref "dept.deptno")) > 30) (BINOP "dept.name" < 3)))))

(define (q2 tables) 
  (SELECT (VALS "t6.c1") 
 FROM (AS (SELECT (VALS "dept0.name") 
  FROM (AS (NAMED (list-ref tables 3)) ["dept0"]) 
  WHERE (BINOP "dept0.name" > 1)) ["t6" (list "c1")]) 
 WHERE (BINOP "t6.c1" > 2) GROUP-BY (list "t6.c1") 
 HAVING (OR (BINOP (VAL-UNOP aggr-count (val-column-ref "t6.c1")) > 30) (BINOP "t6.c1" < 3))))

(define ros-instance (list q1 q2 (list t-info account-info bonus-info dept-info emp-info))) 
 
(define table-info-list (last ros-instance))
(define table-size-list (make-list (length table-info-list) 5))
(define empty-tables (init-sym-tables table-info-list 
                                      (build-list (length table-info-list) (lambda (x) 0))))
(define tables (init-sym-tables table-info-list table-size-list))

(define qt1 (q1 empty-tables))
(define qt2 (q2 empty-tables))

(define c1 (big-step (init-constraint qt1) 20))
(define c2 (big-step (init-constraint qt2) 20))

(define m-tables (init-sym-tables table-info-list table-size-list))
(assert-sym-tables-mconstr m-tables (go-break-symmetry-bounded qt1 qt2))

;(displayln (to-str (go-break-symmetry-bounded qt1 qt2)))

(define (test-now instance tables)
    (let* ([q1 ((list-ref instance 0) tables)]
           [q2 ((list-ref instance 1) tables)])
      ;(println tables)
      (cosette-solve q1 q2 tables)))

;(asserts)
;(time (test-now ros-instance tables))
;(asserts)
;(time (test-now ros-instance m-tables))

(define symvals1 (flatten (map (lambda (t) (Table-content t)) tables)))
(define symvals2 (flatten (map (lambda (t) (Table-content t)) m-tables)))

(time (solve (assert (not (exists symvals2 (bag-equal (get-content (run (q1 m-tables))) (get-content (run (q2 m-tables)))))))))

(time (solve (assert (exists symvals1 (not (bag-equal (get-content (run (q1 tables))) (get-content (run (q2 tables)))))))))

(time (solve (assert 
         (and (exists symvals1 (not (bag-equal (get-content (run (q1 tables))) 
                                               (get-content (run (q2 tables))))))
              (not (exists symvals2 (bag-equal (get-content (run (q1 m-tables)))
                                               (get-content (run (q2 m-tables))))))))))
;(asserts)

;(solve )
