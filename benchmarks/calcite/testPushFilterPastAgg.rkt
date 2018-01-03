#lang rosette 
 
(require "../cosette.rkt" "../sql.rkt" "../evaluator.rkt" "../syntax.rkt") 
 
(provide ros-instance)
 
(current-bitwidth #f)
 
(define-symbolic div_ (~> integer? integer? integer?))
 
(define dept-info (table-info "dept" (list "deptno" "name")))
 

(define (q1 tables) 
  (SELECT (VALS "dept.name" (VAL-UNOP aggr-count (val-column-ref "dept.deptno"))) 
 FROM (NAMED (RENAME (list-ref tables 0) "dept")) 
 WHERE (TRUE) GROUP-BY (list "dept.name") 
 HAVING (BINOP "dept.name" = 10)))

(define (q2 tables) 
  (SELECT (VALS "t2.dname" (VAL-UNOP aggr-count (val-column-ref "t2.dname"))) 
 FROM (AS (SELECT (VALS "dept0.name") 
  FROM (NAMED (RENAME (list-ref tables 0) "dept0")) 
  WHERE (TRUE)) ["t2" (list "dname")]) 
 WHERE (BINOP "t2.dname" = 10) GROUP-BY (list "t2.dname") 
 HAVING (TRUE)))


(define ros-instance (list q1 q2 (list dept-info))) 
