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
  (SELECT (VALS "t3.deptno" "t3.job") 
 FROM (AS (UNION-ALL (SELECT (VALS "emp.deptno" "emp.job") 
 FROM (AS (NAMED (list-ref tables 4)) ["emp"]) 
 WHERE (TRUE) GROUP-BY (list "emp.deptno" "emp.job") 
 HAVING (TRUE)) (SELECT (VALS "emp0.deptno" "emp0.job") 
 FROM (AS (NAMED (list-ref tables 4)) ["emp0"]) 
 WHERE (TRUE) GROUP-BY (list "emp0.deptno" "emp0.job") 
 HAVING (TRUE))) ["t3" (list "deptno" "job")]) 
 WHERE (TRUE) GROUP-BY (list "t3.deptno" "t3.job") 
 HAVING (TRUE)))

(define (q2 tables) 
  (SELECT (VALS "t7.deptno" "t7.job") 
 FROM (AS (UNION-ALL (SELECT (VALS "emp1.deptno" "emp1.job") 
  FROM (AS (NAMED (list-ref tables 4)) ["emp1"]) 
  WHERE (TRUE)) (SELECT (VALS "emp2.deptno" "emp2.job") 
  FROM (AS (NAMED (list-ref tables 4)) ["emp2"]) 
  WHERE (TRUE))) ["t7" (list "deptno" "job")]) 
 WHERE (TRUE) GROUP-BY (list "t7.deptno" "t7.job") 
 HAVING (TRUE)))


(define ros-instance (list q1 q2 (list t-info account-info bonus-info dept-info emp-info))) 
