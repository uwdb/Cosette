#lang rosette 
 
(require "../cosette.rkt" "../util.rkt" "../denotation.rkt" "../cosette.rkt" "../sql.rkt" "../evaluator.rkt" "../syntax.rkt" "../symmetry.rkt") 
  
(current-bitwidth #f)
 
(define-symbolic div_ (~> integer? integer? integer?))
 
(define t-info (table-info "t" (list "k0" "c1" "f1_a0" "f2_a0" "f0_c0" "f1_c0" "f0_c1" "f1_c2" "f2_c3")))
 
(define account-info (table-info "account" (list "acctno" "type" "balance")))
 
(define bonus-info (table-info "bonus" (list "ename" "job" "sal" "comm")))
 
(define dept-info (table-info "dept" (list "deptno" "name")))
 
(define emp-info (table-info "emp" (list "empno" "ename" "job" "mgr" "hiredate" "comm" "sal" "deptno" "slacker")))
 

(define (q1 tables) 
  (SELECT (VALS "t.sal") 
  FROM (AS (UNION-ALL (SELECT (VALS "emp.empno" "emp.ename" "emp.job" "emp.mgr" "emp.hiredate" "emp.comm" "emp.sal" "emp.deptno" "emp.slacker") 
  FROM (AS (NAMED (list-ref tables 4)) ["emp"]) 
  WHERE (TRUE)) (SELECT (VALS "emp0.empno" "emp0.ename" "emp0.job" "emp0.mgr" "emp0.hiredate" "emp0.comm" "emp0.sal" "emp0.deptno" "emp0.slacker") 
  FROM (AS (NAMED (list-ref tables 4)) ["emp0"]) 
  WHERE (TRUE))) ["t" (list "empno" "ename" "job" "mgr" "hiredate" "comm" "sal" "deptno" "slacker")]) 
  WHERE (TRUE)))

(define (q2 tables) 
  (UNION-ALL (SELECT (VALS "emp1.sal") 
  FROM (AS (NAMED (list-ref tables 4)) ["emp1"]) 
  WHERE (TRUE)) (SELECT (VALS "emp2.sal") 
  FROM (AS (NAMED (list-ref tables 4)) ["emp2"]) 
  WHERE (TRUE))))


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

(define m-tables
  (init-sym-tables-mconstr 
    table-info-list 
    table-size-list
    (go-break-symmetry-bounded qt1 qt2)))

(displayln (to-str (go-break-symmetry-bounded qt1 qt2)))

(define (test-now instance tables)
    (let* ([q1 ((list-ref instance 0) tables)]
           [q2 ((list-ref instance 1) tables)])
      ;(println tables)
      (cosette-solve q1 q2 tables)))

;(asserts)
;(time (test-now ros-instance tables))
;(asserts)
(time (test-now ros-instance m-tables))
