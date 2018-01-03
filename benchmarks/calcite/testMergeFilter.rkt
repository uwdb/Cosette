#lang rosette 
 
(require "../cosette.rkt" "../sql.rkt" "../evaluator.rkt" "../syntax.rkt") 
 
(provide ros-instance)
 
(current-bitwidth #f)
 
(define-symbolic div_ (~> integer? integer? integer?))
 
(define dept-info (table-info "dept" (list "deptno" "name")))
 

(define (q1 tables) 
  (SELECT (VALS "t.name") 
  FROM (AS (SELECT (VALS "dept.deptno" "dept.name") 
  FROM (NAMED (RENAME (list-ref tables 0) "dept")) 
  WHERE (BINOP "dept.deptno" = 10)) ["t" (list "deptno" "name")]) 
  WHERE (BINOP "t.deptno" = 10)))

(define (q2 tables) 
  (SELECT (VALS "dept0.name") 
  FROM (NAMED (RENAME (list-ref tables 0) "dept0")) 
  WHERE (BINOP "dept0.deptno" = 10)))


(define ros-instance (list q1 q2 (list dept-info))) 
