#lang rosette

(require "test-util.rkt" "../table.rkt" "../sql.rkt" "../evaluator.rkt" "../equal.rkt")

;;(define (same q1 q2)
  ;;  (assert (bag-equal (get-content (run q1)) (get-content (run q2)))))

(define t1 (Table "R" (list "A" "B") (gen-sym-schema 2 num-rows-in-sym-table)))
(define ta (Table "R" (list "A" "B") concrete-table-2-col))

(define self-join-1
  (SELECT-DISTINCT (VALS "R.A" "R.B")
     FROM (NAMED t1)
     WHERE (filter-empty)))

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
