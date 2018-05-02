#lang rosette 
 
(require "../cosette.rkt" "../util.rkt" "../denotation.rkt" "../cosette.rkt" "../sql.rkt" "../evaluator.rkt" "../syntax.rkt" "../symmetry.rkt" "../test-util.rkt") 
  

(provide ros-instance)  

(current-bitwidth #f)

(define t0 (table-info "input" (list "c1" "c2" "c3" "c4" "c5")))
 
(define (q3 tables) 
(SELECT (VALS "t3.c1" "t3.c2" "t3.c31" "t3.c4" "t3.c51" )
 FROM (AS (JOIN (AS (SELECT (VALS "t4.c3" "t4.c5" )
 FROM (AS (NAMED (list-ref tables 0)) ["t4" (list "c1" "c2" "c3" "c4" "c5")])
 WHERE (TRUE)
 GROUP-BY (list "t4.c3" "t4.c5" )
 HAVING (TRUE)) ["t2" (list "c3" "c5")]) (AS (NAMED (list-ref tables 0)) ["t1" (list "c1" "c2" "c3" "c4" "c5")])) ["t3" (list "c3" "c5" "c1" "c2" "c31" "c4" "c51")])
 WHERE (AND (BINOP "t3.c3" = "t3.c31") (BINOP "t3.c5" (lambda (x y) (not (equal? x y))) "t3.c51"))))
 
(define (q2 tables) 
(SELECT (VALS "t2.c1" "t2.c2" "t2.c3" "t2.c4" "t2.c5" )
 FROM (AS (JOIN (NAMED (list-ref tables 0)) (AS (NAMED (list-ref tables 0)) ["t1" (list "c1" "c2" "c3" "c4" "c5")])) ["t2" (list "c1" "c2" "c3" "c4" "c5" "c11" "c21" "c31" "c41" "c51")])
 WHERE (AND (BINOP "t2.c3" = "t2.c31") (BINOP "t2.c5" (lambda (x y) (not (equal? x y))) "t2.c51"))))
 
(define (q1 tables) 
(SELECT (VALS "t2.c1" "t2.c2" "t2.c31" "t2.c41" "t2.c51" )
 FROM (AS (JOIN (AS (SELECT (VALS "t1.c3" "t1.c4" "t1.c5" )
 FROM (AS (NAMED (list-ref tables 0)) ["t1" (list "c1" "c2" "c3" "c4" "c5")])
 WHERE (TRUE)
 GROUP-BY (list "t1.c3" "t1.c4" "t1.c5" )
 HAVING (TRUE)) ["t3" (list "c3" "c4" "c5")]) (AS (NAMED (list-ref tables 0)) ["t4" (list "c1" "c2" "c3" "c4" "c5")])) ["t2" (list "c3" "c4" "c5" "c1" "c2" "c31" "c41" "c51")])
 WHERE (AND (BINOP "t2.c3" = "t2.c31") (BINOP "t2.c5" (lambda (x y) (not (equal? x y))) "t2.c51"))))

(define ros-instance (list q1 q2 (list t0)))
