#lang rosette

(require "../util.rkt" "../sql.rkt" "../table.rkt"  "../evaluator.rkt" "../equal.rkt")

(define t1 (Table "t1" (list "c1" "c2" "c3") (gen-sym-schema 3 2)))

; commutativity of selection query 1
(define push-selection-q1
  (SELECT (VALS "t2.c1" "t2.c2" "t2.c3")
          FROM  (AS (SELECT (VALS "t1.c1" "t1.c2" "t1.c3")
                                FROM (NAMED t1)
                                WHERE (BINOP "t1.c1" < "t1.c2"))
                    ["t2" (list "c1" "c2" "c3")])
          WHERE  (BINOP "t2.c1" < "t2.c3")))

; commutativity of selection query 2
(define push-selection-q2
    (SELECT (VALS "t1.c1" "t1.c2" "t1.c3")
	       FROM   (NAMED t1)
               WHERE  (AND (BINOP "t1.c1" < "t1.c2") (BINOP "t1.c1" < "t1.c3"))))

(time (verify (same push-selection-q1 push-selection-q2)))