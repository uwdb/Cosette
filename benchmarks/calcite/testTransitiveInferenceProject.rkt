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
  (SELECT (VALS 1) 
  FROM (JOIN (AS (SELECT (VALS "emp.empno" "emp.ename" "emp.job" "emp.mgr" "emp.hiredate" "emp.comm" "emp.sal" "emp.deptno" "emp.slacker") 
  FROM (AS (NAMED (list-ref tables 4)) ["emp"]) 
  WHERE (BINOP "emp.deptno" > 7)) ["t" (list "empno" "ename" "job" "mgr" "hiredate" "comm" "sal" "deptno" "slacker")]) (AS (NAMED (list-ref tables 4)) ["emp0"])) 
  WHERE (BINOP "t.deptno" = "emp0.deptno")))

(define (q2 tables) 
  (SELECT (VALS 1) 
  FROM (JOIN (AS (SELECT (VALS "emp1.empno" "emp1.ename" "emp1.job" "emp1.mgr" "emp1.hiredate" "emp1.comm" "emp1.sal" "emp1.deptno" "emp1.slacker") 
  FROM (AS (NAMED (list-ref tables 4)) ["emp1"]) 
  WHERE (BINOP "emp1.deptno" > 7)) ["t1" (list "empno" "ename" "job" "mgr" "hiredate" "comm" "sal" "deptno" "slacker")]) (AS (SELECT (VALS "emp2.empno" "emp2.ename" "emp2.job" "emp2.mgr" "emp2.hiredate" "emp2.comm" "emp2.sal" "emp2.deptno" "emp2.slacker") 
  FROM (AS (NAMED (list-ref tables 4)) ["emp2"]) 
  WHERE (BINOP "emp2.deptno" > 7)) ["t2" (list "empno" "ename" "job" "mgr" "hiredate" "comm" "sal" "deptno" "slacker")])) 
  WHERE (BINOP "t1.deptno" = "t2.deptno")))


(define ros-instance (list q1 q2 (list t-info account-info bonus-info dept-info emp-info))) 
