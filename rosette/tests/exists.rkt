#lang rosette 
 
(require "../cosette.rkt" "../sql.rkt" "../evaluator.rkt" "../syntax.rkt" "../test-util.rkt") 
 
 (provide ros-instance)
 
(current-bitwidth #f)
 
(define-symbolic div_ (~> integer? integer? integer?))
 
(define b-info (table-info "b" (list "yb" "yc")))
 
(define a-info (table-info "a" (list "x" "ya")))
 

(define (q1 tables) 
  (SELECT-DISTINCT (VALS "a.x") 
  FROM (AS (NAMED (list-ref tables 1)) ["a"]) 
  WHERE (NOT (EXISTS (AS (SELECT (VALS "b.yb" "b.yc") 
  FROM (AS (NAMED (list-ref tables 0)) ["b"])
  WHERE (OR (BINOP "b.yb" < "a.ya") (BINOP "b.yb" > "a.ya"))) ["anyname" (list "yb" "yc")])))))

(define (q2 tables)
  (SELECT-DISTINCT (VALS "a.x") 
  FROM (AS (NAMED (list-ref tables 1)) ["a"])
  WHERE (BINOP (AGGR-SUBQ aggr-count (SELECT (VALS "b.yb") 
 FROM (AS (NAMED (list-ref tables 0)) ["b"])
 WHERE (BINOP "b.yb" = "a.ya") GROUP-BY (list) 
 HAVING (TRUE))) = (AGGR-SUBQ aggr-count (SELECT (VALS "c.yb") 
 FROM (AS (NAMED (list-ref tables 0)) ["c"])
 WHERE (TRUE) GROUP-BY (list)
 HAVING (TRUE))))))

(define ros-instance (list q1 q2 (list b-info a-info))) 

(run-experiment ros-instance #f #f #f)