#lang rosette 
 
(require "../cosette.rkt" "../util.rkt" "../denotation.rkt" "../cosette.rkt" "../sql.rkt" "../evaluator.rkt" "../syntax.rkt" "../symmetry.rkt" "../test-util.rkt") 
  
(provide ros-instance)  

(current-bitwidth #f)

(define t0 (table-info "input" (list "ID" "CHARGEID" "CHARGETYPE" "SERVICEMONTH")))
 
(define (q3 tables) 
(SELECT (VALS "t1.ID" "t1.CHARGEID" "t1.CHARGETYPE" "t1.max_SERVICEMONTH" )
 FROM (AS (JOIN (AS (SELECT (VALS "t4.CHARGEID" (VAL-UNOP aggr-max (val-column-ref "t4.SERVICEMONTH")) )
 FROM (AS (NAMED (list-ref tables 0)) ["t4" (list "ID" "CHARGEID" "CHARGETYPE" "SERVICEMONTH")])
 WHERE (TRUE)
 GROUP-BY (list "t4.CHARGEID" )
 HAVING (TRUE)) ["t3" (list "CHARGEID" "max_SERVICEMONTH")]) (AS (NAMED (list-ref tables 0)) ["t2" (list "ID" "CHARGEID" "CHARGETYPE" "SERVICEMONTH")])) ["t1" (list "CHARGEID" "max_SERVICEMONTH" "ID" "CHARGEID1" "CHARGETYPE" "SERVICEMONTH")])
 WHERE (AND (BINOP "t1.max_SERVICEMONTH" = "t1.SERVICEMONTH") (BINOP "t1.CHARGEID" = "t1.CHARGEID1"))))
 
(define (q2 tables) 
(SELECT (VALS "t4.ID" "t4.CHARGEID" "t4.CHARGETYPE" "t4.max_SERVICEMONTH" )
 FROM (AS (JOIN (AS (SELECT (VALS "t1.CHARGEID" "t1.CHARGETYPE" (VAL-UNOP aggr-max (val-column-ref "t1.SERVICEMONTH")) )
 FROM (AS (NAMED (list-ref tables 0)) ["t1" (list "ID" "CHARGEID" "CHARGETYPE" "SERVICEMONTH")])
 WHERE (TRUE)
 GROUP-BY (list "t1.CHARGEID" "t1.CHARGETYPE" )
 HAVING (TRUE)) ["t2" (list "CHARGEID" "CHARGETYPE" "max_SERVICEMONTH")]) (AS (NAMED (list-ref tables 0)) ["t3" (list "ID" "CHARGEID" "CHARGETYPE" "SERVICEMONTH")])) ["t4" (list "CHARGEID" "CHARGETYPE" "max_SERVICEMONTH" "ID" "CHARGEID1" "CHARGETYPE1" "SERVICEMONTH")])
 WHERE (AND (BINOP "t4.max_SERVICEMONTH" = "t4.SERVICEMONTH") (BINOP "t4.CHARGEID" = "t4.CHARGEID1"))))
 
(define (q1 tables) 
(SELECT (VALS "t2.ID" "t2.CHARGEID" "t2.CHARGETYPE" "t2.max_SERVICEMONTH" )
 FROM (AS (JOIN (AS (SELECT (VALS "t1.CHARGETYPE" (VAL-UNOP aggr-max (val-column-ref "t1.SERVICEMONTH")) )
 FROM (AS (NAMED (list-ref tables 0)) ["t1" (list "ID" "CHARGEID" "CHARGETYPE" "SERVICEMONTH")])
 WHERE (TRUE)
 GROUP-BY (list "t1.CHARGETYPE" )
 HAVING (TRUE)) ["t4" (list "CHARGETYPE" "max_SERVICEMONTH")]) (AS (NAMED (list-ref tables 0)) ["t3" (list "ID" "CHARGEID" "CHARGETYPE" "SERVICEMONTH")])) ["t2" (list "CHARGETYPE" "max_SERVICEMONTH" "ID" "CHARGEID" "CHARGETYPE1" "SERVICEMONTH")])
 WHERE (AND (BINOP "t2.max_SERVICEMONTH" = "t2.SERVICEMONTH") (BINOP "t2.CHARGETYPE" = "t2.CHARGETYPE1"))))

(define ros-instance (list q1 q2 (list t0)))
