;//http://stackoverflow.com/questions/39957816/get-unique-values-in-table-by-multiple-criteria

#lang rosette 
 
(require "../table.rkt" "../cosette.rkt" "../util.rkt" "../denotation.rkt" "../cosette.rkt" "../sql.rkt" "../evaluator.rkt" "../syntax.rkt" "../symmetry.rkt" "../test-util.rkt") 

(current-bitwidth #f)

(define-symbolic div_ (~> integer? integer? integer?))

(define picture-info (table-info "picture" (list "uid" "size")))

(define user-info (table-info "user" (list "uid" "uname" "city")))

;; several test xproduct
(define content-a
  (list
    (cons (list 0 1000001) 14)))

(define content-b
  (list
    (cons (list 0 0 3) 7)))

(define table1 (Table "picture" '("uid" "size") content-a))
(define table2 (Table "user" '("uid" "uname" "city") content-b))

(define tables (list table1 table2))

(define (q1 tables)
  (SELECT (VALS "x.uid" "x.uname" (AGGR-SUBQ aggr-count (SELECT (VALS "y.uid")
 FROM (AS (NAMED (list-ref tables 0)) ["y"])
 WHERE (AND (BINOP "x.uid" = "y.uid") (BINOP "y.size" > 1000000)) GROUP-BY (list)
 HAVING (TRUE))))
  FROM (AS (NAMED (list-ref tables 1)) ["x"])
  WHERE (BINOP "x.city" = 3)))

(define (q2 tables)
  (SELECT (VALS "x.uid" "x.uname" (COUNT (val-column-ref "y.uid")))
 FROM (JOIN (AS (NAMED (list-ref tables 1)) ["x"]) (AS (NAMED (list-ref tables 0)) ["y"]))
 WHERE (AND (AND (BINOP "x.uid" = "y.uid") (BINOP "y.size" > 1000000)) (BINOP "x.city" = 3)) GROUP-BY (list "x.uid" "x.uname")
 HAVING (TRUE)))

(define (q3 tables)
  (SELECT (VALS "y.uid")
 FROM (AS (NAMED (list-ref tables 0)) ["y"])
 WHERE (AND (BINOP 0 = "y.uid") (BINOP "y.size" > 1000000)) 
 GROUP-BY (list)
 HAVING (TRUE)))

;(define ros-instance (list q1 q2 (list picture-info user-info)))

;(run-experiment ros-instance #f #f #f)

(run (q1 tables))
(run (q2 tables))
(run (q3 tables))
