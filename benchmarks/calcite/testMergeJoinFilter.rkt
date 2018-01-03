#lang rosette 
 
(require "../cosette.rkt" "../sql.rkt" "../evaluator.rkt" "../syntax.rkt") 
 
(provide ros-instance)
 
(current-bitwidth #f)
 
(define-symbolic div_ (~> integer? integer? integer?))
 
(define dept-info (table-info "dept" (list "deptno" "name")))
 
(define emp-info (table-info "emp" (list "empno" "ename" "job" "mgr" "hiredate" "comm" "sal" "deptno" "slacker")))
 

(define (q1 tables) 
  (SELECT (VALS "t.deptno" "t.ename") 
  FROM (AS (SELECT (VALS "dept.deptno" "emp.ename") 
  FROM (JOIN (NAMED (RENAME (list-ref tables 1) "emp")) (NAMED (RENAME (list-ref tables 0) "dept"))) 
  WHERE (AND (BINOP "emp.deptno" = "dept.deptno") (BINOP "dept.deptno" = 10))) ["t" (list "deptno" "ename")]) 
  WHERE (BINOP "t.deptno" = 10)))

(define (q2 tables) 
  (SELECT (VALS "t1.deptno" "emp0.ename") 
  FROM (JOIN (NAMED (RENAME (list-ref tables 1) "emp0")) (AS (SELECT (VALS "dept0.deptno" "dept0.name") 
  FROM (NAMED (RENAME (list-ref tables 0) "dept0")) 
  WHERE (BINOP "dept0.deptno" = 10)) ["t1" (list "deptno" "name")])) 
  WHERE (BINOP "emp0.deptno" = "t1.deptno")))


(define ros-instance (list q1 q2 (list dept-info emp-info))) 
