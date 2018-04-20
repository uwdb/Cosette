#lang rosette 
 
(require "../cosette.rkt" "../util.rkt" "../denotation.rkt" "../cosette.rkt" "../sql.rkt" "../evaluator.rkt" "../syntax.rkt" "../symmetry.rkt" "../test-util.rkt") 
  
(current-bitwidth #f)

(define t0 (table-info "input" (list "ID" "DocumentID" "Status" "DateCreated")))
 
(define (q4 tables) 
(SELECT (VALS "t4.DocumentID" "t4.Status" "t4.max_DateCreated" )
 FROM (AS (JOIN (AS (SELECT (VALS "t1.DocumentID" (VAL-UNOP aggr-max (val-column-ref "t1.DateCreated")) )
 FROM (AS (SELECT (VALS "input.ID" "input.DocumentID" "input.Status" "input.DateCreated" )
 FROM (NAMED (list-ref tables 0))
 WHERE (AND (BINOP "input.ID" > "input.DocumentID") (TRUE))) ["t1" (list "ID" "DocumentID" "Status" "DateCreated")])
 WHERE (TRUE)
 GROUP-BY (list "t1.DocumentID" )
 HAVING (TRUE)) ["t2" (list "DocumentID" "max_DateCreated")]) (AS (NAMED (list-ref tables 0)) ["t3" (list "ID" "DocumentID" "Status" "DateCreated")])) ["t4" (list "DocumentID" "max_DateCreated" "ID" "DocumentID1" "Status" "DateCreated")])
 WHERE (AND (BINOP "t4.DocumentID" = "t4.DocumentID1") (BINOP "t4.max_DateCreated" = "t4.DateCreated"))))
 
(define (q3 tables) 
(SELECT (VALS "t4.DocumentID" "t4.Status" "t4.DateCreated" )
 FROM (AS (JOIN (AS (SELECT (VALS "t1.DocumentID" (VAL-UNOP aggr-max (val-column-ref "t1.ID")) )
 FROM (AS (SELECT (VALS "input.ID" "input.DocumentID" "input.Status" "input.DateCreated" )
 FROM (NAMED (list-ref tables 0))
 WHERE (AND (BINOP "input.ID" > "input.DocumentID") (TRUE))) ["t1" (list "ID" "DocumentID" "Status" "DateCreated")])
 WHERE (TRUE)
 GROUP-BY (list "t1.DocumentID" )
 HAVING (TRUE)) ["t2" (list "DocumentID" "max_ID")]) (AS (NAMED (list-ref tables 0)) ["t3" (list "ID" "DocumentID" "Status" "DateCreated")])) ["t4" (list "DocumentID" "max_ID" "ID" "DocumentID1" "Status" "DateCreated")])
 WHERE (AND (BINOP "t4.DocumentID" = "t4.DocumentID1") (BINOP "t4.max_ID" = "t4.ID"))))
 
(define (q2 tables) 
(SELECT (VALS "t2.DocumentID" "t2.Status" "t2.max_DateCreated" )
 FROM (AS (JOIN (AS (SELECT (VALS "t3.DocumentID" (VAL-UNOP aggr-max (val-column-ref "t3.DateCreated")) )
 FROM (AS (NAMED (list-ref tables 0)) ["t3" (list "ID" "DocumentID" "Status" "DateCreated")])
 WHERE (TRUE)
 GROUP-BY (list "t3.DocumentID" )
 HAVING (TRUE)) ["t4" (list "DocumentID" "max_DateCreated")]) (AS (NAMED (list-ref tables 0)) ["t1" (list "ID" "DocumentID" "Status" "DateCreated")])) ["t2" (list "DocumentID" "max_DateCreated" "ID" "DocumentID1" "Status" "DateCreated")])
 WHERE (AND (BINOP "t2.DocumentID" = "t2.DocumentID1") (BINOP "t2.max_DateCreated" = "t2.DateCreated"))))
 
(define (q1 tables) 
(SELECT (VALS "t3.DocumentID" "t3.Status" "t3.DateCreated" )
 FROM (AS (JOIN (AS (SELECT (VALS "t4.DocumentID" (VAL-UNOP aggr-max (val-column-ref "t4.ID")) )
 FROM (AS (NAMED (list-ref tables 0)) ["t4" (list "ID" "DocumentID" "Status" "DateCreated")])
 WHERE (TRUE)
 GROUP-BY (list "t4.DocumentID" )
 HAVING (TRUE)) ["t1" (list "DocumentID" "max_ID")]) (AS (NAMED (list-ref tables 0)) ["t2" (list "ID" "DocumentID" "Status" "DateCreated")])) ["t3" (list "DocumentID" "max_ID" "ID" "DocumentID1" "Status" "DateCreated")])
 WHERE (AND (BINOP "t3.DocumentID" = "t3.DocumentID1") (BINOP "t3.max_ID" = "t3.ID"))))

(define ros-instance (list q1 q2 (list t0)))
