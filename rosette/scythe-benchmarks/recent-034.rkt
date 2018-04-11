#lang rosette 
 
(require "../cosette.rkt" "../util.rkt" "../denotation.rkt" "../cosette.rkt" "../sql.rkt" "../evaluator.rkt" "../syntax.rkt" "../symmetry.rkt" "../test-util.rkt") 
  

(provide ros-instance)  

(current-bitwidth #f)

(define t0 (table-info "input" (list "MATERIAL" "DISCO_DATE" "DATE_UPDATE")))
 
(define (q5 tables) 
(SELECT (VALS "t2.MATERIAL" "t2.DISCO_DATE1" "t2.DATE_UPDATE1" )
 FROM (AS (JOIN (NAMED (list-ref tables 0)) (AS (NAMED (list-ref tables 0)) ["t1" (list "MATERIAL" "DISCO_DATE" "DATE_UPDATE")])) ["t2" (list "MATERIAL" "DISCO_DATE" "DATE_UPDATE" "MATERIAL1" "DISCO_DATE1" "DATE_UPDATE1")])
 WHERE (AND (BINOP "t2.DISCO_DATE" < "t2.DISCO_DATE1") (TRUE))))
 
(define (q4 tables) 
(SELECT (VALS "t1.MATERIAL" "t1.DISCO_DATE" "t1.max_DATE_UPDATE" )
 FROM (AS (JOIN (AS (SELECT (VALS "t4.MATERIAL" (VAL-UNOP aggr-max (val-column-ref "t4.DATE_UPDATE")) )
 FROM (AS (SELECT (VALS "input.MATERIAL" "input.DISCO_DATE" "input.DATE_UPDATE" )
 FROM (NAMED (list-ref tables 0))
 WHERE (AND (BINOP "input.DISCO_DATE" equal? sqlnull) (TRUE))) ["t4" (list "MATERIAL" "DISCO_DATE" "DATE_UPDATE")])
 WHERE (TRUE)
 GROUP-BY (list "t4.MATERIAL" )
 HAVING (TRUE)) ["t3" (list "MATERIAL" "max_DATE_UPDATE")]) (AS (NAMED (list-ref tables 0)) ["t2" (list "MATERIAL" "DISCO_DATE" "DATE_UPDATE")])) ["t1" (list "MATERIAL" "max_DATE_UPDATE" "MATERIAL1" "DISCO_DATE" "DATE_UPDATE")])
 WHERE (AND (TRUE) (BINOP "t1.max_DATE_UPDATE" = "t1.DATE_UPDATE"))))
 
(define (q3 tables) 
(SELECT (VALS "t4.MATERIAL" "t4.max_DISCO_DATE" "t4.DATE_UPDATE" )
 FROM (AS (JOIN (AS (SELECT (VALS "t1.MATERIAL" (VAL-UNOP aggr-max (val-column-ref "t1.DISCO_DATE")) )
 FROM (AS (SELECT (VALS "input.MATERIAL" "input.DISCO_DATE" "input.DATE_UPDATE" )
 FROM (NAMED (list-ref tables 0))
 WHERE (AND (BINOP "input.DISCO_DATE" equal? sqlnull) (TRUE))) ["t1" (list "MATERIAL" "DISCO_DATE" "DATE_UPDATE")])
 WHERE (TRUE)
 GROUP-BY (list "t1.MATERIAL" )
 HAVING (TRUE)) ["t2" (list "MATERIAL" "max_DISCO_DATE")]) (AS (NAMED (list-ref tables 0)) ["t3" (list "MATERIAL" "DISCO_DATE" "DATE_UPDATE")])) ["t4" (list "MATERIAL" "max_DISCO_DATE" "MATERIAL1" "DISCO_DATE" "DATE_UPDATE")])
 WHERE (AND (TRUE) (BINOP "t4.max_DISCO_DATE" = "t4.DISCO_DATE"))))
 
(define (q2 tables) 
(SELECT (VALS "t4.MATERIAL" "t4.DISCO_DATE" "t4.max_DATE_UPDATE" )
 FROM (AS (JOIN (AS (SELECT (VALS (VAL-UNOP aggr-max (val-column-ref "t3.DATE_UPDATE")) )
 FROM (AS (SELECT (VALS "input.MATERIAL" "input.DISCO_DATE" "input.DATE_UPDATE" )
 FROM (NAMED (list-ref tables 0))
 WHERE (AND (BINOP "input.DISCO_DATE" equal? sqlnull) (TRUE))) ["t3" (list "MATERIAL" "DISCO_DATE" "DATE_UPDATE")])
 WHERE (TRUE)
 GROUP-BY (list )
 HAVING (TRUE)) ["t1" (list "max_DATE_UPDATE")]) (AS (NAMED (list-ref tables 0)) ["t2" (list "MATERIAL" "DISCO_DATE" "DATE_UPDATE")])) ["t4" (list "max_DATE_UPDATE" "MATERIAL" "DISCO_DATE" "DATE_UPDATE")])
 WHERE (AND (TRUE) (BINOP "t4.max_DATE_UPDATE" = "t4.DATE_UPDATE"))))
 
(define (q1 tables) 
(SELECT (VALS "t3.MATERIAL" "t3.max_DISCO_DATE" "t3.DATE_UPDATE" )
 FROM (AS (JOIN (AS (SELECT (VALS (VAL-UNOP aggr-max (val-column-ref "t1.DISCO_DATE")) )
 FROM (AS (SELECT (VALS "input.MATERIAL" "input.DISCO_DATE" "input.DATE_UPDATE" )
 FROM (NAMED (list-ref tables 0))
 WHERE (AND (BINOP "input.DISCO_DATE" equal? sqlnull) (TRUE))) ["t1" (list "MATERIAL" "DISCO_DATE" "DATE_UPDATE")])
 WHERE (TRUE)
 GROUP-BY (list )
 HAVING (TRUE)) ["t2" (list "max_DISCO_DATE")]) (AS (NAMED (list-ref tables 0)) ["t4" (list "MATERIAL" "DISCO_DATE" "DATE_UPDATE")])) ["t3" (list "max_DISCO_DATE" "MATERIAL" "DISCO_DATE" "DATE_UPDATE")])
 WHERE (AND (BINOP "t3.max_DISCO_DATE" = "t3.DISCO_DATE") (TRUE))))

(define ros-instance (list q1 q2 (list t0)))
