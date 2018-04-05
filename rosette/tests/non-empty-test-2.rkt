#lang rosette 
 
(require "../cosette.rkt" "../util.rkt" "../table.rkt" "../denotation.rkt" "../cosette.rkt" "../sql.rkt" "../evaluator.rkt" "../syntax.rkt" "../symmetry.rkt") 
  
(current-bitwidth #f)
 
(define-symbolic div_ (~> integer? integer? integer?))

(define t-info (table-info "t" (list "k0" "c1" "f1_a0" "f2_a0" "f0_c0" "f1_c0" "f0_c1" "f1_c2" "f2_c3")))
 
(define account-info (table-info "account" (list "acctno" "type" "balance")))
 
(define bonus-info (table-info "bonus" (list "ename" "job" "sal" "comm")))
 
(define dept-info (table-info "dept" (list "deptno" "name")))
 
(define emp-info (table-info "emp" (list "empno" "ename" "job" "mgr" "hiredate" "comm" "sal" "deptno" "slacker")))
 
(define-symbolic* str_charlie_ integer?) 

(define (q1 tables) 
  (SELECT (VALS "dept.name" "dept.deptno" (VAL-UNOP aggr-count (val-column-ref "dept.deptno"))) 
 FROM (AS (NAMED (list-ref tables 3)) ["dept"]) 
 WHERE (TRUE) GROUP-BY (list "dept.name" "dept.deptno") 
 HAVING (BINOP "dept.name" = str_charlie_)))

(define empty-out (Table "empty-out" (list "dname" "ddeptno" "aggr-dname") (list)))

(define (q2 tables) (NAMED empty-out))

(define ros-instance (list q1 q2 (list t-info account-info bonus-info dept-info emp-info))) 

(define table-info-list (last ros-instance))
(define table-size-list (make-list (length table-info-list) 10))
(define empty-tables (init-sym-tables table-info-list 
                                      (build-list (length table-info-list) (lambda (x) 0))))
(define tables (init-sym-tables table-info-list table-size-list))

(define qt1 (q1 empty-tables))
(define qt2 (q2 empty-tables))

(define c1 (big-step (init-constraint qt1) 20))
(define c2 (big-step (init-constraint qt2) 20))

(define m-tables (init-sym-tables table-info-list table-size-list))
(assert-sym-tables-mconstr m-tables (go-break-symmetry-bounded qt1 qt2))

(displayln (go-break-symmetry-bounded qt1 qt2))

(define (test-now instance tables)
    (let* ([q1 ((list-ref instance 0) tables)]
           [q2 ((list-ref instance 1) tables)])
      ;(println tables)
      (cosette-solve q1 q2 tables)))

(time (test-now ros-instance m-tables))
(time (test-now ros-instance tables))
