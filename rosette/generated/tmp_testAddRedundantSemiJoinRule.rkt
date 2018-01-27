#lang rosette 
 
(require "../cosette.rkt" "../sql.rkt" "../evaluator.rkt" "../syntax.rkt") 
 
(provide ros-instance)
 
(current-bitwidth #f)
 
(define-symbolic div_ (~> integer? integer? integer?))
 
(define dept-info (table-info "dept" (list "deptno" "name")))
 
(define emp-info (table-info "emp" (list "empno" "ename" "job" "mgr" "hiredate" "comm" "sal" "deptno" "slacker")))
 

(define (q1 tables) 
  (SELECT (VALS 1) 
  FROM (JOIN (AS (NAMED (list-ref tables 1)) ["emp"]) (AS (NAMED (list-ref tables 0)) ["dept"])) 
  WHERE (BINOP "emp.deptno" = "dept.deptno")))

(define (q2 tables) 
  (SELECT (VALS 1) 
  FROM (JOIN (AS (NAMED (list-ref tables 1)) ["emp0"]) (JOIN (AS (NAMED (list-ref tables 0)) ["dept0"]) (AS (NAMED (list-ref tables 0)) ["dept1"]))) 
  WHERE (AND (BINOP "emp0.deptno" = "dept0.deptno") (BINOP "emp0.deptno" = "dept1.deptno"))))


(define ros-instance (list q1 q2 (list dept-info emp-info))) 
