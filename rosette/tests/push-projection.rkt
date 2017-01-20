#lang rosette

(require "../util.rkt" "../table.rkt" "../sql.rkt" "../evaluator.rkt" "../equal.rkt")

(define sx (Table "x" (list "a" "k" "g") (gen-sym-schema 3 2)))
(define sy (Table "y" (list "a" "k" "g") (gen-sym-schema 3 2)))

; push projection query 1
(define push-projection-q1
  (SELECT (VALS "x.a")
   FROM (JOIN (NAMED sx) (NAMED sy))
   WHERE (BINOP "x.k" eq? "y.k")))

; push projection query 2
(define push-projection-q2
  (SELECT (VALS "x1.a")
          FROM (JOIN (AS (SELECT (VALS "x.a" "x.k")
                                 FROM (NAMED sx)
                                 WHERE (filter-empty))
                         ["x1" (list "a" "k")])
                     (NAMED sy))
          WHERE (BINOP "x1.k" eq? "y.k")))

;(run inner-query)
;(run push-projection-q1)
;(run push-projection-q2)
(time (verify (same push-projection-q1 push-projection-q2)))
