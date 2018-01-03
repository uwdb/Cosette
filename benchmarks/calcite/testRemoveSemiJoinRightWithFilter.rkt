#lang rosette 
 
(require "../cosette.rkt" "../sql.rkt" "../evaluator.rkt" "../syntax.rkt") 
 
(provide ros-instance)
 
(current-bitwidth #f)
 
(define-symbolic div_ (~> integer? integer? integer?))
 
(define dept-info (table-info "dept" (list "deptno" "name")))
 
(define emp-info (table-info "emp" (list "empno" "ename" "job" "mgr" "hiredate" "comm" "sal" "deptno" "slacker")))
 
(define-symbolic* str_foo_ integer?) 

(define (q1 tables) 
  (SELECT (VALS "emp.ename") 
  FROM (JOIN (NAMED (RENAME (list-ref tables 1) "emp")) (JOIN (NAMED (RENAME (list-ref tables 0) "dept")) (NAMED (RENAME (list-ref tables 1) "emp0")))) 
  WHERE (AND (AND (BINOP "emp.deptno" = "dept.deptno") (BINOP "dept.deptno" = "emp0.deptno")) (BINOP "dept.name" = str_foo_))))

(define (q2 tables) 
  (SELECT (VALS "emp1.ename") 
  FROM (JOIN (NAMED (RENAME (list-ref tables 1) "emp1")) (JOIN (AS (SELECT (VALS "dept0.deptno" "dept0.name") 
  FROM (NAMED (RENAME (list-ref tables 0) "dept0")) 
  WHERE (BINOP "dept0.name" = str_foo_)) ["t1" (list "deptno" "name")]) (NAMED (RENAME (list-ref tables 1) "emp2")))) 
  WHERE (AND (BINOP "emp1.deptno" = "t1.deptno") (BINOP "t1.deptno" = "emp2.deptno"))))


(define ros-instance (list q1 q2 (list dept-info emp-info))) 
