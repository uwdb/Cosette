#lang rosette 
 
(require "../cosette.rkt" "../sql.rkt" "../evaluator.rkt" "../syntax.rkt") 
 
(provide ros-instance)
 
(current-bitwidth #f)
 
(define-symbolic div_ (~> integer? integer? integer?))
 
(define emp-info (table-info "emp" (list "empno" "ename" "job" "mgr" "hiredate" "comm" "sal" "deptno" "slacker")))
 

(define (q1 tables) 
  (SELECT (VALS "emp.deptno" (VAL-UNOP aggr-sum (val-column-ref "emp.sal")) "emp.empno") 
 FROM (NAMED (RENAME (list-ref tables 0) "emp")) 
 WHERE (TRUE) GROUP-BY (list "emp.deptno" "emp.empno") 
 HAVING (TRUE)))

(define (q2 tables) 
  (SELECT (VALS "emp0.deptno" (VAL-UNOP aggr-sum (val-column-ref "emp0.sal")) "emp0.empno") 
 FROM (NAMED (RENAME (list-ref tables 0) "emp0")) 
 WHERE (TRUE) GROUP-BY (list "emp0.empno" "emp0.deptno") 
 HAVING (TRUE)))


(define ros-instance (list q1 q2 (list emp-info))) 
