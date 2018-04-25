#lang rosette 
 
(require "../cosette.rkt" "../util.rkt" "../denotation.rkt" "../cosette.rkt" "../sql.rkt" "../evaluator.rkt" "../syntax.rkt" "../symmetry.rkt" "../test-util.rkt") 
  

(provide ros-instance)  

(current-bitwidth #f)

(define t0 (table-info "input" (list "c1" "c2")))
 
(define (q2 tables) 
(SELECT (VALS "t5.max_c1" )
 FROM (AS (JOIN (AS (SELECT (VALS "t4.c2" (VAL-UNOP aggr-max (val-column-ref "t4.c1")) )
 FROM (AS (NAMED (list-ref tables 0)) ["t4" (list "c1" "c2")])
 WHERE (TRUE)
 GROUP-BY (list "t4.c2" )
 HAVING (TRUE)) ["t3" (list "c2" "max_c1")]) (AS (SELECT (VALS "t2.c1" (VAL-UNOP aggr-max (val-column-ref "t2.c2")) )
 FROM (AS (NAMED (list-ref tables 0)) ["t2" (list "c1" "c2")])
 WHERE (TRUE)
 GROUP-BY (list "t2.c1" )
 HAVING (TRUE)) ["t1" (list "c1" "max_c2")])) ["t5" (list "c2" "max_c1" "c1" "max_c2")])
 WHERE (AND (BINOP "t5.c2" = "t5.max_c2") (BINOP "t5.max_c1" > "t5.c1"))))
 
(define (q1 tables) 
(SELECT (VALS "t5.max_c1" )
 FROM (AS (JOIN (AS (SELECT (VALS "t4.c1" (VAL-UNOP aggr-max (val-column-ref "t4.c2")) )
 FROM (AS (NAMED (list-ref tables 0)) ["t4" (list "c1" "c2")])
 WHERE (TRUE)
 GROUP-BY (list "t4.c1" )
 HAVING (TRUE)) ["t3" (list "c1" "max_c2")]) (AS (SELECT (VALS "t2.c2" (VAL-UNOP aggr-max (val-column-ref "t2.c1")) )
 FROM (AS (NAMED (list-ref tables 0)) ["t2" (list "c1" "c2")])
 WHERE (TRUE)
 GROUP-BY (list "t2.c2" )
 HAVING (TRUE)) ["t1" (list "c2" "max_c1")])) ["t5" (list "c1" "max_c2" "c2" "max_c1")])
 WHERE (AND (BINOP "t5.c1" < "t5.max_c1") (BINOP "t5.max_c2" = "t5.c2"))))

(define ros-instance (list q1 q2 (list t0)))
