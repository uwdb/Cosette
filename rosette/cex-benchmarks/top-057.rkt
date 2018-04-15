#lang rosette 
 
(require "../cosette.rkt" "../util.rkt" "../denotation.rkt" "../cosette.rkt" "../sql.rkt" "../evaluator.rkt" "../syntax.rkt" "../symmetry.rkt" "../test-util.rkt") 
  
(provide ros-instance)  

(current-bitwidth #f)

(define t0 (table-info "input" (list "ID" "Name" "City" "Birthyear")))
 
(define (q3 tables) 
(SELECT (VALS "t3.Name" "t3.City" "t3.Birthyear" )
 FROM (AS (JOIN (AS (SELECT (VALS (VAL-UNOP aggr-min (val-column-ref "t4.ID")) )
 FROM (AS (NAMED (list-ref tables 0)) ["t4" (list "ID" "Name" "City" "Birthyear")])
 WHERE (TRUE)
 GROUP-BY (list )
 HAVING (TRUE)) ["t2" (list "min_ID")]) (AS (NAMED (list-ref tables 0)) ["t1" (list "ID" "Name" "City" "Birthyear")])) ["t3" (list "min_ID" "ID" "Name" "City" "Birthyear")])
 WHERE (AND (BINOP "t3.min_ID" < "t3.ID") (TRUE))))
 
(define (q2 tables) 
(SELECT (VALS "t1.Name" "t1.City" "t1.Birthyear" )
 FROM (AS (JOIN (AS (SELECT (VALS "t4.City" (VAL-UNOP aggr-max (val-column-ref "t4.ID")) )
 FROM (AS (NAMED (list-ref tables 0)) ["t4" (list "ID" "Name" "City" "Birthyear")])
 WHERE (TRUE)
 GROUP-BY (list "t4.City" )
 HAVING (TRUE)) ["t3" (list "City" "max_ID")]) (AS (NAMED (list-ref tables 0)) ["t2" (list "ID" "Name" "City" "Birthyear")])) ["t1" (list "City" "max_ID" "ID" "Name" "City1" "Birthyear")])
 WHERE (AND (BINOP "t1.max_ID" = "t1.ID") (TRUE))))
 
(define (q1 tables) 
(SELECT (VALS "t4.Name" "t4.City" "t4.min_Birthyear" )
 FROM (AS (JOIN (AS (SELECT (VALS "t1.City" (VAL-UNOP aggr-min (val-column-ref "t1.Birthyear")) )
 FROM (AS (NAMED (list-ref tables 0)) ["t1" (list "ID" "Name" "City" "Birthyear")])
 WHERE (TRUE)
 GROUP-BY (list "t1.City" )
 HAVING (TRUE)) ["t2" (list "City" "min_Birthyear")]) (AS (NAMED (list-ref tables 0)) ["t3" (list "ID" "Name" "City" "Birthyear")])) ["t4" (list "City" "min_Birthyear" "ID" "Name" "City1" "Birthyear")])
 WHERE (AND (BINOP "t4.min_Birthyear" = "t4.Birthyear") (TRUE))))

(define ros-instance (list q1 q2 (list t0)))
