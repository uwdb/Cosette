#lang rosette 
 
(require "../cosette.rkt" "../sql.rkt" "../evaluator.rkt" "../syntax.rkt") 
 
(provide ros-instance)
 
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
 FROM (NAMED (RENAME (list-ref tables 3) "dept")) 
 WHERE (TRUE) GROUP-BY (list "dept.name" "dept.deptno") 
 HAVING (BINOP "dept.name" = str_charlie_)))

(define (q2 tables) 
  (SELECT (VALS "t3.dname" "t3.ddeptno" (VAL-UNOP aggr-count (val-column-ref "t2.dname"))) 
 FROM (AS (SELECT (VALS "dept0.name" "dept0.deptno") 
  FROM (NAMED (RENAME (list-ref tables 3) "dept0")) 
  WHERE (TRUE)) ["t2" (list "dname" "ddeptno")]) 
 WHERE (BINOP "t2.dname" = str_charlie_) GROUP-BY (list "t3.dname" "t3.ddeptno") 
 HAVING (TRUE)))


(define ros-instance (list q1 q2 (list t-info account-info bonus-info dept-info emp-info))) 
