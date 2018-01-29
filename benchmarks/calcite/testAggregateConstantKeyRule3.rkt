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
 
(define-symbolic* str_null_ integer?) 
(define-symbolic* str_clerk_ integer?) 

(define (q1 tables) 
  (SELECT (VALS "emp.job") 
 FROM (AS (NAMED (list-ref tables 4)) ["emp"]) 
 WHERE (AND (BINOP "emp.sal" = str_null_) (BINOP "emp.job" = str_clerk_)) GROUP-BY (list "emp.sal" "emp.job") 
 HAVING (BINOP (VAL-UNOP aggr-count (val-column-ref "emp.empno")) > 3)))

(define (q2 tables) 
  (SELECT (VALS "t7.job") 
  FROM (AS (SELECT (VALS "emp0.sal" str_clerk_ (VAL-UNOP aggr-count (val-column-ref "emp0.empno"))) 
 FROM (AS (NAMED (list-ref tables 4)) ["emp0"]) 
 WHERE (AND (BINOP "emp0.sal" = str_null_) (BINOP "emp0.job" = str_clerk_)) GROUP-BY (list "emp0.sal") 
 HAVING (TRUE)) ["t7" (list "sal" "job" "f2")]) 
  WHERE (BINOP "t7.f2" > 3)))


(define ros-instance (list q1 q2 (list t-info account-info bonus-info dept-info emp-info))) 
