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
 

(define (q1 tables) 
  (SELECT (VALS "t0.ename" "t0.sal" "t0.deptno") 
 FROM (AS (SELECT (VALS "emp.ename" "emp.sal" "emp.deptno") 
  FROM (AS (NAMED (list-ref tables 4)) ["emp"]) 
  WHERE (TRUE)) ["t" (list "ename" "sal" "deptno")]) 
 WHERE (BINOP "t.sal" > 5000) GROUP-BY (list "t0.ename" "t0.sal" "t0.deptno") 
 HAVING (TRUE)))

(define (q2 tables) 
  (SELECT (VALS "t4.ename" "t4.sal" "t4.deptno") 
 FROM (AS (SELECT (VALS "emp0.ename" "emp0.sal" "emp0.deptno") 
 FROM (AS (NAMED (list-ref tables 4)) ["emp0"]) 
 WHERE (TRUE) GROUP-BY (list "emp0.ename" "emp0.sal" "emp0.deptno") 
 HAVING (BINOP "emp0.sal" > 5000)) ["t4" (list "ename" "sal" "deptno")]) 
 WHERE (TRUE) GROUP-BY (list "t4.ename" "t4.sal" "t4.deptno") 
 HAVING (TRUE)))


(define ros-instance (list q1 q2 (list t-info account-info bonus-info dept-info emp-info))) 
