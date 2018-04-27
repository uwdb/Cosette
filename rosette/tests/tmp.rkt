#lang rosette 
 
(require "../cosette.rkt" "../sql.rkt" "../evaluator.rkt" "../syntax.rkt" "../table.rkt") 
  
(current-bitwidth #f)
 
(define-symbolic div_ (~> integer? integer? integer?))
 
(define b-info (table-info "b" (list "yb" "yc")))
 
(define a-info (table-info "a" (list "x" "ya")))
 
 
 (define test-table1
  (list
    (cons (list 1 1) 2)
    (cons (list 1 2) 2)))
 
  (define test-table2
  (list
    (cons (list 3 3) 2)))
 
(define table1 (Table "a" (list "x" "ya") test-table1))
(define table2 (Table "b" (list "yb" "yc") test-table2))

(define tables (list table2 table1))


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
 WHERE (BINOP "b.yb" = "a.ya"))) = (AGGR-SUBQ aggr-count (SELECT (VALS "b.yb") 
 FROM (AS (NAMED (list-ref tables 0)) ["b"]) 
 WHERE (TRUE))))))

(run (q1 tables))
(run (q2 tables))