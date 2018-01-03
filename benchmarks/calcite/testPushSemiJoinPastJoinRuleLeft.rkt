#lang rosette 
 
(require "../cosette.rkt" "../sql.rkt" "../evaluator.rkt" "../syntax.rkt") 
 
(provide ros-instance)
 
(current-bitwidth #f)
 
(define-symbolic div_ (~> integer? integer? integer?))
 
(define dept-info (table-info "dept" (list "deptno" "name")))
 
(define emp-info (table-info "emp" (list "empno" "ename" "job" "mgr" "hiredate" "comm" "sal" "deptno" "slacker")))
 

(define (q1 tables) 
  (SELECT (VALS "emp.ename") 
  FROM (JOIN (NAMED (RENAME (list-ref tables 1) "emp")) (JOIN (NAMED (RENAME (list-ref tables 0) "dept")) (NAMED (RENAME (list-ref tables 1) "emp0")))) 
  WHERE (AND (BINOP "emp.deptno" = "dept.deptno") (BINOP "emp.empno" = "emp0.empno"))))

(define (q2 tables) 
  (SELECT (VALS "emp1.ename") 
  FROM (JOIN (NAMED (RENAME (list-ref tables 1) "emp1")) (JOIN (NAMED (RENAME (list-ref tables 0) "dept0")) (JOIN (NAMED (RENAME (list-ref tables 1) "emp2")) (JOIN (NAMED (RENAME (list-ref tables 0) "dept1")) (NAMED (RENAME (list-ref tables 1) "emp3")))))) 
  WHERE (AND (AND (AND (BINOP "emp1.deptno" = "dept0.deptno") (BINOP "emp1.empno" = "emp2.empno")) (BINOP "emp1.deptno" = "dept1.deptno")) (BINOP "emp1.empno" = "emp3.empno"))))


(define ros-instance (list q1 q2 (list dept-info emp-info))) 
