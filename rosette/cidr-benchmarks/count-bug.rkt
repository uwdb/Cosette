#lang rosette

(require "../util.rkt" "../sql.rkt" "../table.rkt"  "../evaluator.rkt" "../equal.rkt"  rosette/lib/synthax)

; ------- actual tables (only for test) -------

(define parts-example
  (Table "parts" (list "pnum" "qoh")
         (list
          (cons (list 0 0) 8)
          (cons (list 2 2) 15))))

(define supply-example
  (Table "supply" (list "pnum" "shipdate")
         (list
          (cons (list 2 9) 2))))

; ------------ symbolic tables ----------------
; we need at least two rows

(define sym-parts (Table "parts" (list "pnum" "qoh") (gen-sym-schema 2 2)))

(define sym-supply (Table "supply" (list "pnum" "shipdate") (gen-sym-schema 2 1)))
(assert-table-non-empty sym-supply)

; ------------ count bug ----------------------
(define parts sym-parts)
(define supply sym-supply)

;SELECT pnum FROM parts
;WHERE qoh = (SELECT COUNT(shipdate) FROM supply
;             WHERE supply.pnum = parts.pnum AND shipdate < 10 )
(define count-bug-q1
  (SELECT
   (VALS "parts.pnum")
   FROM (NAMED parts)
   WHERE (BINOP "parts.qoh" = 
                (AGGR-SUBQ aggr-count
                      (SELECT
                       (VALS "supply.shipdate")
                       FROM (NAMED supply)
                       WHERE (AND (BINOP "supply.pnum" = "parts.pnum")
                                  (BINOP "supply.shipdate" < 10))))
                )))

; SELECT pnum, count(shipdate)
; FROM supply WHERE shipdate < 10
; GROUP BY pnum
(define temp
  (SELECT-DISTINCT
   (VALS
    "supply.pnum"
    (AGGR-SUBQ aggr-count
          (SELECT
           (VALS "s2.shipdate")
           FROM (AS (NAMED supply) ["s2" (list "pnum" "shipdate")])
           WHERE (AND (BINOP "s2.pnum" = "supply.pnum")
                      (BINOP "s2.shipdate" < 10))
           )))
   FROM (NAMED supply)
   WHERE (BINOP "supply.shipdate" < 10)))

(define count-bug-q2
  (SELECT
   (VALS "parts.pnum")
   FROM (JOIN (NAMED parts) (AS temp ["temp" (list "suppnum" "ct")]))
   WHERE (AND (BINOP "parts.qoh" = "temp.ct")
              (BINOP "parts.pnum" = "temp.suppnum"))
   ))


; for printing constraints in the paper
;(define paper (Table "parts" (list "pnum" "qoh") (gen-sym-schema 2 1)))
;(define paper32
;  (SELECT
;   (VALS "parts.pnum")
;   FROM (NAMED paper)
;   WHERE (BINOP "parts.qoh" = 1)))
; expect model
;(run count-bug-q1)
;(run paper32)

;(run (NAMED parts-example))
;(print supply)
;(run (NAMED supply))
;(solve count-bug-q2)
(time (verify (same count-bug-q1 count-bug-q2)))





