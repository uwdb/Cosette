#lang rosette 
 
(require "../cosette.rkt" "../util.rkt" "../denotation.rkt" "../cosette.rkt" "../sql.rkt" "../evaluator.rkt" "../syntax.rkt" "../symmetry.rkt" "../test-util.rkt") 
  

(provide ros-instance)  

(current-bitwidth #f)

(define t0 (table-info "input" (list "CustomerID" "Balance" "Date")))
 
(define (q2 tables) 
(SELECT (VALS "t4.CustomerID" "t4.Balance" "t4.Date" )
 FROM (AS (JOIN (AS (SELECT (VALS "t1.CustomerID" (VAL-UNOP aggr-max (val-column-ref "t1.Date")) )
 FROM (AS (SELECT (VALS "input.CustomerID" "input.Balance" "input.Date" )
 FROM (NAMED (list-ref tables 0))
 WHERE (AND (BINOP "input.Balance" > 0.0) (TRUE))) ["t1" (list "CustomerID" "Balance" "Date")])
 WHERE (TRUE)
 GROUP-BY (list "t1.CustomerID" )
 HAVING (TRUE)) ["t2" (list "CustomerID" "max_Date")]) (AS (NAMED (list-ref tables 0)) ["t3" (list "CustomerID" "Balance" "Date")])) ["t4" (list "CustomerID" "max_Date" "CustomerID1" "Balance" "Date")])
 WHERE (AND (TRUE) (BINOP "t4.max_Date" < "t4.Date"))))
 
(define (q1 tables) 
(SELECT (VALS "t3.CustomerID" "t3.Balance" "t3.Date" )
 FROM (AS (JOIN (AS (SELECT (VALS (VAL-UNOP aggr-max (val-column-ref "t4.Date")) )
 FROM (AS (SELECT (VALS "input.CustomerID" "input.Balance" "input.Date" )
 FROM (NAMED (list-ref tables 0))
 WHERE (AND (BINOP "input.Balance" > 0.0) (TRUE))) ["t4" (list "CustomerID" "Balance" "Date")])
 WHERE (TRUE)
 GROUP-BY (list )
 HAVING (TRUE)) ["t2" (list "max_Date")]) (AS (NAMED (list-ref tables 0)) ["t1" (list "CustomerID" "Balance" "Date")])) ["t3" (list "max_Date" "CustomerID" "Balance" "Date")])
 WHERE (AND (BINOP "t3.max_Date" < "t3.Date") (TRUE))))

(define ros-instance (list q1 q2 (list t0)))