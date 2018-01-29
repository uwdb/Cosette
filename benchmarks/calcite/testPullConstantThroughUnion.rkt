#lang rosette 
 
(require "../cosette.rkt" "../sql.rkt" "../evaluator.rkt" "../syntax.rkt") 
 
(provide ros-instance)
 
(current-bitwidth #f)
 
(define-symbolic div_ (~> integer? integer? integer?))
 
(define emp-info (table-info "emp" (list "empno" "ename" "job" "mgr" "hiredate" "comm" "sal" "deptno" "slacker")))
 

(define (q1 tables) 
  (UNION-ALL (SELECT (VALS 2 "emp.deptno" "emp.job") 
  FROM (AS (NAMED (list-ref tables 0)) ["emp"]) 
  WHERE (TRUE)) (SELECT (VALS 2 "emp0.deptno" "emp0.job") 
  FROM (AS (NAMED (list-ref tables 0)) ["emp0"]) 
  WHERE (TRUE))))

(define (q2 tables) 
  (SELECT (VALS 2 "t6.deptno" "t6.job") 
  FROM (AS (UNION-ALL (SELECT (VALS "emp1.deptno" "emp1.job") 
  FROM (AS (NAMED (list-ref tables 0)) ["emp1"]) 
  WHERE (TRUE)) (SELECT (VALS "emp2.deptno" "emp2.job") 
  FROM (AS (NAMED (list-ref tables 0)) ["emp2"]) 
  WHERE (TRUE))) ["t6" (list "deptno" "job")]) 
  WHERE (TRUE)))


(define ros-instance (list q1 q2 (list emp-info))) 
