#lang rosette 
 
(require "../cosette.rkt" "../util.rkt" "../denotation.rkt" "../cosette.rkt" "../sql.rkt" "../evaluator.rkt" "../syntax.rkt" "../symmetry.rkt" "../test-util.rkt") 
  
(provide ros-instance)  

(current-bitwidth #f)

(define t0 (table-info "input" (list "cname" "wmname" "avg")))
 
(define (q2 tables) 
(SELECT (VALS "t2.cname1" "t2.wmname1" "t2.avg1" )
 FROM (AS (JOIN (NAMED (list-ref tables 0)) (AS (NAMED (list-ref tables 0)) ["t1" (list "cname" "wmname" "avg")])) ["t2" (list "cname" "wmname" "avg" "cname1" "wmname1" "avg1")])
 WHERE (AND (BINOP "t2.avg" < "t2.avg1") (BINOP "t2.cname" (lambda (x y) (not (equal? x y))) "t2.cname1"))))
 
(define (q1 tables) 
(SELECT (VALS "t1.cname" "t1.wmname" "t1.max_avg" )
 FROM (AS (JOIN (AS (SELECT (VALS "t4.cname" (VAL-UNOP aggr-max (val-column-ref "t4.avg")) )
 FROM (AS (NAMED (list-ref tables 0)) ["t4" (list "cname" "wmname" "avg")])
 WHERE (TRUE)
 GROUP-BY (list "t4.cname" )
 HAVING (TRUE)) ["t3" (list "cname" "max_avg")]) (AS (NAMED (list-ref tables 0)) ["t2" (list "cname" "wmname" "avg")])) ["t1" (list "cname" "max_avg" "cname1" "wmname" "avg")])
 WHERE (AND (TRUE) (BINOP "t1.max_avg" = "t1.avg"))))

(define ros-instance (list q1 q2 (list t0)))
