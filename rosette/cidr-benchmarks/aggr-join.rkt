#lang rosette

(require "../util.rkt" "../sql.rkt" "../table.rkt"  "../evaluator.rkt" "../equal.rkt")

; (define t1 (Table "t1" (list "c1" "c2" "c3") (gen-sym-schema 3 3)))
; (define ta (Table "R" (list "A" "B") concrete-table-2-col))
; (define tb (Table "S" (list "C" "D") concrete-table-2-col))

(define ta (Table "R" (list "A" "B") (gen-sym-schema 2 2)))
(define tb (Table "S" (list "C" "D") (gen-sym-schema 2 2)))

(define subq-aggr-1
  (SELECT-DISTINCT (VALS "R.A" (AGGR aggr-sum 
                                     (SELECT (VALS "S2.D")
                                             FROM (JOIN (AS (NAMED ta) ["R2" (list "A" "B")]) 
                                                        (AS (NAMED tb) ["S2" (list "C" "D")]))
                                             WHERE (BINOP "R.A" = "R2.A"))))
                   FROM (JOIN (NAMED ta) (NAMED tb))
                   WHERE (BINOP "R.B" = "S.C")))

(define part-subq-2 
  (SELECT-DISTINCT (VALS "S.C" (AGGR aggr-sum
                                     (SELECT (VALS "S2.D")
                                             FROM (AS (NAMED tb) ["S2" (list "C" "D")])
                                             WHERE (BINOP "S2.C" = "S.C"))))
                   FROM (NAMED tb)
                   WHERE (TRUE)))

(define subq-aggr-2
  (SELECT-DISTINCT (VALS "R.A" (AGGR aggr-sum 
                                     (SELECT (VALS "S3.D")
                                             FROM (JOIN (AS (NAMED ta) ["R2" (list "A" "B")]) 
                                                        (AS (NAMED tb) ["S3" (list "C" "D")]))
                                             WHERE (BINOP "R.A" = "R2.A"))))
                   FROM (JOIN (NAMED ta) (AS part-subq-2 ["S3" (list "C" "D")]))
                   WHERE (BINOP "R.B" = "S3.C")))

;(run subq-aggr-1)
;(run subq-aggr-2)

; commutativity of selection query 1

; commutativity of selection query 2

(time (verify (same subq-aggr-1 subq-aggr-2)))

