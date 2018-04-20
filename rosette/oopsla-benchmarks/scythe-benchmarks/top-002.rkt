
#lang rosette 
 
(require "../cosette.rkt" "../util.rkt" "../denotation.rkt" "../cosette.rkt" "../sql.rkt" "../evaluator.rkt" "../syntax.rkt" "../symmetry.rkt" "../test-util.rkt") 
  

(provide ros-instance)  

(current-bitwidth #f)

(define t0 (table-info "input" (list "ID" "NAME" "EMAIL")))
 
(define (q5 tables) 
(SELECT (VALS "t2.NAME" )
 FROM (AS (SELECT (VALS "t1.NAME" (VAL-UNOP aggr-count (val-column-ref "t1.ID")) )
 FROM (AS (SELECT (VALS "input.ID" "input.NAME" "input.EMAIL" )
 FROM (NAMED (list-ref tables 0))
 WHERE (AND (BINOP "input.ID" > 1.0) (TRUE))) ["t1" (list "ID" "NAME" "EMAIL")])
 WHERE (TRUE)
 GROUP-BY (list "t1.NAME" )
 HAVING (TRUE)) ["t2" (list "NAME" "count_ID")])
 WHERE (AND (BINOP "t2.count_ID" > 1.0) (TRUE))))
 
(define (q4 tables) 
(SELECT (VALS "t1.NAME" )
 FROM (AS (SELECT (VALS "t2.NAME" (VAL-UNOP aggr-count (val-column-ref "t2.NAME")) )
 FROM (AS (SELECT (VALS "input.ID" "input.NAME" "input.EMAIL" )
 FROM (NAMED (list-ref tables 0))
 WHERE (AND (BINOP "input.ID" > 1.0) (TRUE))) ["t2" (list "ID" "NAME" "EMAIL")])
 WHERE (TRUE)
 GROUP-BY (list "t2.NAME" )
 HAVING (TRUE)) ["t1" (list "NAME" "count_NAME")])
 WHERE (AND (BINOP "t1.count_NAME" > 1.0) (TRUE))))
 
(define (q3 tables) 
(SELECT (VALS "t1.NAME" )
 FROM (AS (SELECT (VALS "t2.NAME" "t2.EMAIL" (VAL-UNOP aggr-count (val-column-ref "t2.EMAIL")) )
 FROM (AS (SELECT (VALS "input.ID" "input.NAME" "input.EMAIL" )
 FROM (NAMED (list-ref tables 0))
 WHERE (AND (BINOP "input.ID" > 1.0) (TRUE))) ["t2" (list "ID" "NAME" "EMAIL")])
 WHERE (TRUE)
 GROUP-BY (list "t2.NAME" "t2.EMAIL" )
 HAVING (TRUE)) ["t1" (list "NAME" "EMAIL" "count_EMAIL")])
 WHERE (AND (BINOP "t1.count_EMAIL" > 1.0) (TRUE))))
 
(define (q2 tables) 
(SELECT (VALS "t2.NAME" )
 FROM (AS (SELECT (VALS "t1.NAME" "t1.EMAIL" (VAL-UNOP aggr-count (val-column-ref "t1.NAME")) )
 FROM (AS (SELECT (VALS "input.ID" "input.NAME" "input.EMAIL" )
 FROM (NAMED (list-ref tables 0))
 WHERE (AND (BINOP "input.ID" > 1.0) (TRUE))) ["t1" (list "ID" "NAME" "EMAIL")])
 WHERE (TRUE)
 GROUP-BY (list "t1.NAME" "t1.EMAIL" )
 HAVING (TRUE)) ["t2" (list "NAME" "EMAIL" "count_NAME")])
 WHERE (AND (BINOP "t2.count_NAME" > 1.0) (TRUE))))
 
(define (q1 tables) 
(SELECT (VALS "t1.NAME" )
 FROM (AS (SELECT (VALS "t2.NAME" "t2.EMAIL" (VAL-UNOP aggr-count (val-column-ref "t2.ID")) )
 FROM (AS (SELECT (VALS "input.ID" "input.NAME" "input.EMAIL" )
 FROM (NAMED (list-ref tables 0))
 WHERE (AND (BINOP "input.ID" > 1.0) (TRUE))) ["t2" (list "ID" "NAME" "EMAIL")])
 WHERE (TRUE)
 GROUP-BY (list "t2.NAME" "t2.EMAIL" )
 HAVING (TRUE)) ["t1" (list "NAME" "EMAIL" "count_ID")])
 WHERE (AND (BINOP "t1.count_ID" > 1.0) (TRUE))))

(define ros-instance (list q1 q5 (list t0)))
