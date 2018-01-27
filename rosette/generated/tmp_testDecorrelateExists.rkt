#lang rosette 
 
(require "../cosette.rkt" "../sql.rkt" "../evaluator.rkt" "../syntax.rkt") 
 
(provide ros-instance)
 
(current-bitwidth #f)
 
(define-symbolic div_ (~> integer? integer? integer?))
 
(define emp-info (table-info "emp" (list "empno" "ename" "job" "mgr" "hiredate" "comm" "sal" "deptno" "slacker")))
 

(define (q1 tables) 
  (SELECT (VALS "emp.empno" "emp.ename" "emp.job" "emp.mgr" "emp.hiredate" "emp.comm" "emp.sal" "emp.deptno" "emp.slacker") 
  FROM (AS (NAMED (list-ref tables 0)) ["emp"]) 
  WHERE (EXISTS (AS (SELECT (VALS "emp0.empno" "emp0.ename" "emp0.job" "emp0.mgr" "emp0.hiredate" "emp0.comm" "emp0.sal" "emp0.deptno" "emp0.slacker") 
  FROM (AS (NAMED (list-ref tables 0)) ["emp0"]) 
  WHERE (BINOP "emp.deptno" = "emp0.deptno")) ["anyname" (list "empno" "ename" "job" "mgr" "hiredate" "comm" "sal" "deptno" "slacker")]))))

(define (q2 tables) 
  (SELECT (VALS "emp1.empno" "emp1.ename" "emp1.job" "emp1.mgr" "emp1.hiredate" "emp1.comm" "emp1.sal" "emp1.deptno" "emp1.slacker") 
  FROM (JOIN (AS (NAMED (list-ref tables 0)) ["emp1"]) (AS (SELECT (VALS "emp2.deptno" 1) 
 FROM (AS (NAMED (list-ref tables 0)) ["emp2"]) 
 WHERE (TRUE) GROUP-BY (list "emp2.deptno") 
 HAVING (TRUE)) ["t4" (list "deptno" "f1")])) 
  WHERE (BINOP "emp1.deptno" = "t4.deptno")))


(define ros-instance (list q1 q2 (list emp-info))) 
