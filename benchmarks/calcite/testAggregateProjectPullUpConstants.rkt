#lang rosette 
 
(require "../cosette.rkt" "../sql.rkt" "../evaluator.rkt" "../syntax.rkt") 
 
(provide ros-instance)
 
(current-bitwidth #f)
 
(define-symbolic div_ (~> integer? integer? integer?))
 
(define emp-info (table-info "emp" (list "empno" "ename" "job" "mgr" "hiredate" "comm" "sal" "deptno" "slacker")))
 

(define (q1 tables) 
  (SELECT (VALS "emp.job" "emp.empno" "emp.sal" (VAL-UNOP aggr-sum (val-column-ref "emp.sal"))) 
 FROM (NAMED (RENAME (list-ref tables 0) "emp")) 
 WHERE (BINOP "emp.empno" = 10) GROUP-BY (list "emp.job" "emp.empno" "emp.sal") 
 HAVING (TRUE)))

(define (q2 tables) 
  (SELECT (VALS "emp0.job" 10 "emp0.sal" (VAL-UNOP aggr-sum (val-column-ref "emp0.sal"))) 
 FROM (NAMED (RENAME (list-ref tables 0) "emp0")) 
 WHERE (BINOP "emp0.empno" = 10) GROUP-BY (list "emp0.job" "emp0.sal") 
 HAVING (TRUE)))


(define ros-instance (list q1 q2 (list emp-info))) 
