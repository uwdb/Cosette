#lang rosette 
 
(require "../cosette.rkt" "../util.rkt" "../denotation.rkt" "../cosette.rkt" "../sql.rkt" "../evaluator.rkt" "../syntax.rkt" "../symmetry.rkt" "../test-util.rkt") 
  
(provide ros-instance)  

(current-bitwidth #f)

(define t0 (table-info "input" (list "id" "user" "time" "io")))
 
(define (q2 tables) 
(SELECT (VALS "t1.id" "t1.user" "t1.max_time" "t1.io" )
 FROM (AS (JOIN (AS (SELECT (VALS "t4.user" (VAL-UNOP aggr-max (val-column-ref "t4.time")) )
 FROM (AS (NAMED (list-ref tables 0)) ["t4" (list "id" "user" "time" "io")])
 WHERE (TRUE)
 GROUP-BY (list "t4.user" )
 HAVING (TRUE)) ["t3" (list "user" "max_time")]) (AS (NAMED (list-ref tables 0)) ["t2" (list "id" "user" "time" "io")])) ["t1" (list "user" "max_time" "id" "user1" "time" "io")])
 WHERE (AND (BINOP "t1.user" = "t1.user1") (BINOP "t1.max_time" = "t1.time"))))
 
(define (q1 tables) 
(SELECT (VALS "t4.max_id" "t4.user" "t4.time" "t4.io" )
 FROM (AS (JOIN (AS (SELECT (VALS "t3.user" (VAL-UNOP aggr-max (val-column-ref "t3.id")) )
 FROM (AS (NAMED (list-ref tables 0)) ["t3" (list "id" "user" "time" "io")])
 WHERE (TRUE)
 GROUP-BY (list "t3.user" )
 HAVING (TRUE)) ["t2" (list "user" "max_id")]) (AS (NAMED (list-ref tables 0)) ["t1" (list "id" "user" "time" "io")])) ["t4" (list "user" "max_id" "id" "user1" "time" "io")])
 WHERE (AND (TRUE) (BINOP "t4.max_id" = "t4.id"))))

(define ros-instance (list q1 q2 (list t0)))

