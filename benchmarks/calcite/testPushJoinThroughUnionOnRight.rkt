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
  (SELECT (VALS "emp.sal") 
  FROM (JOIN (AS (NAMED (list-ref tables 4)) ["emp"]) (AS (UNION-ALL (SELECT (VALS "emp0.empno" "emp0.ename" "emp0.job" "emp0.mgr" "emp0.hiredate" "emp0.comm" "emp0.sal" "emp0.deptno" "emp0.slacker") 
  FROM (AS (NAMED (list-ref tables 4)) ["emp0"]) 
  WHERE (TRUE)) (SELECT (VALS "emp1.empno" "emp1.ename" "emp1.job" "emp1.mgr" "emp1.hiredate" "emp1.comm" "emp1.sal" "emp1.deptno" "emp1.slacker") 
  FROM (AS (NAMED (list-ref tables 4)) ["emp1"]) 
  WHERE (TRUE))) ["t" (list "empno" "ename" "job" "mgr" "hiredate" "comm" "sal" "deptno" "slacker")])) 
  WHERE (TRUE)))

(define (q2 tables) 
  (SELECT (VALS "t1.sal") 
  FROM (AS (UNION-ALL (SELECT (VALS "emp2.empno" "emp2.ename" "emp2.job" "emp2.mgr" "emp2.hiredate" "emp2.comm" "emp2.sal" "emp2.deptno" "emp2.slacker" "emp3.empno" "emp3.ename" "emp3.job" "emp3.mgr" "emp3.hiredate" "emp3.comm" "emp3.sal" "emp3.deptno" "emp3.slacker") 
  FROM (JOIN (AS (NAMED (list-ref tables 4)) ["emp2"]) (AS (NAMED (list-ref tables 4)) ["emp3"])) 
  WHERE (TRUE)) (SELECT (VALS "emp4.empno" "emp4.ename" "emp4.job" "emp4.mgr" "emp4.hiredate" "emp4.comm" "emp4.sal" "emp4.deptno" "emp4.slacker" "emp5.empno" "emp5.ename" "emp5.job" "emp5.mgr" "emp5.hiredate" "emp5.comm" "emp5.sal" "emp5.deptno" "emp5.slacker") 
  FROM (JOIN (AS (NAMED (list-ref tables 4)) ["emp4"]) (AS (NAMED (list-ref tables 4)) ["emp5"])) 
  WHERE (TRUE))) ["t1" (list "empno" "ename" "job" "mgr" "hiredate" "comm" "sal" "deptno" "slacker" "empno" "ename" "job" "mgr" "hiredate" "comm" "sal" "deptno" "slacker")]) 
  WHERE (TRUE)))


(define ros-instance (list q1 q2 (list t-info account-info bonus-info dept-info emp-info))) 
