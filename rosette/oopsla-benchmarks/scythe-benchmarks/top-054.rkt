#lang rosette 
 
(require "../cosette.rkt" "../util.rkt" "../denotation.rkt" "../cosette.rkt" "../sql.rkt" "../evaluator.rkt" "../syntax.rkt" "../symmetry.rkt" "../test-util.rkt") 
  
(provide ros-instance)  

(current-bitwidth #f)

(define t0 (table-info "input" (list "created_at" "count")))
 
(define (q4 tables) 
(SELECT (VALS "t4.created_at" "t4.sum_count1" )
 FROM (AS (SELECT (VALS "t2.created_at" "t2.count" (VAL-UNOP aggr-sum (val-column-ref "t2.count1")) )
 FROM (AS (SELECT (VALS "t5.created_at" "t5.count" "t5.created_at1" "t5.count1" )
 FROM (AS (JOIN (NAMED (list-ref tables 0)) (AS (NAMED (list-ref tables 0)) ["t3" (list "created_at" "count")])) ["t5" (list "created_at" "count" "created_at1" "count1")])
 WHERE (AND (BINOP "t5.created_at" >= "t5.created_at1") (TRUE))) ["t2" (list "created_at" "count" "created_at1" "count1")])
 WHERE (TRUE)
 GROUP-BY (list "t2.created_at" "t2.count" )
 HAVING (TRUE)) ["t4" (list "created_at" "count" "sum_count1")])
 WHERE (TRUE)))
 
(define (q3 tables) 
(AS (SELECT (VALS "t5.created_at" (VAL-UNOP aggr-sum (val-column-ref "t5.count1")) )
 FROM (AS (SELECT (VALS "t3.created_at" "t3.count" "t3.created_at1" "t3.count1" )
 FROM (AS (JOIN (NAMED (list-ref tables 0)) (AS (NAMED (list-ref tables 0)) ["t2" (list "created_at" "count")])) ["t3" (list "created_at" "count" "created_at1" "count1")])
 WHERE (AND (BINOP "t3.created_at" >= "t3.created_at1") (TRUE))) ["t5" (list "created_at" "count" "created_at1" "count1")])
 WHERE (TRUE)
 GROUP-BY (list "t5.created_at" )
 HAVING (TRUE)) ["t4" (list "created_at" "sum_count1")]))
 
(define (q2 tables) 
(AS (SELECT (VALS "t2.created_at1" (VAL-UNOP aggr-sum (val-column-ref "t2.count")) )
 FROM (AS (SELECT (VALS "t3.created_at" "t3.count" "t3.created_at1" "t3.count1" )
 FROM (AS (JOIN (NAMED (list-ref tables 0)) (AS (NAMED (list-ref tables 0)) ["t4" (list "created_at" "count")])) ["t3" (list "created_at" "count" "created_at1" "count1")])
 WHERE (AND (TRUE) (BINOP "t3.created_at" <= "t3.created_at1"))) ["t2" (list "created_at" "count" "created_at1" "count1")])
 WHERE (TRUE)
 GROUP-BY (list "t2.created_at1" )
 HAVING (TRUE)) ["t5" (list "created_at1" "sum_count")]))
 
(define (q1 tables) 
(SELECT (VALS "t4.created_at1" "t4.sum_count" )
 FROM (AS (SELECT (VALS "t5.created_at1" "t5.count1" (VAL-UNOP aggr-sum (val-column-ref "t5.count")) )
 FROM (AS (SELECT (VALS "t3.created_at" "t3.count" "t3.created_at1" "t3.count1" )
 FROM (AS (JOIN (NAMED (list-ref tables 0)) (AS (NAMED (list-ref tables 0)) ["t2" (list "created_at" "count")])) ["t3" (list "created_at" "count" "created_at1" "count1")])
 WHERE (AND (TRUE) (BINOP "t3.created_at" <= "t3.created_at1"))) ["t5" (list "created_at" "count" "created_at1" "count1")])
 WHERE (TRUE)
 GROUP-BY (list "t5.created_at1" "t5.count1" )
 HAVING (TRUE)) ["t4" (list "created_at1" "count1" "sum_count")])
 WHERE (TRUE)))

(define ros-instance (list q1 q2 (list t0)))
