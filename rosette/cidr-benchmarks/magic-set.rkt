#lang rosette

(require "../util.rkt" "../sql.rkt" "../table.rkt"  "../evaluator.rkt" "../equal.rkt")

(define t1 (Table "R" (list "A" "B") (gen-sym-schema 2 2)))

(define self-join-1
  (SELECT-DISTINCT (VALS "R.A" "R.B")
     FROM (NAMED t1)
     WHERE (F-EMPTY)))

(define self-join-2
  (SELECT-DISTINCT (VALS "X.A" "X.B")
     FROM (JOIN (AS (NAMED t1) ["X" (list "A" "B")]) 
		(AS (NAMED t1) ["Y" (list "A" "B")]))
     WHERE (AND (BINOP "X.A" = "Y.A") (BINOP "X.B" = "Y.B"))))

;(run self-join-1)
;(run self-join-2)

; commutativity of selection query 1

; commutativity of selection query 2

(time (verify (same self-join-1 self-join-2)))
