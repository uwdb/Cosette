#lang rosette

(require "../util.rkt" "../sql.rkt" "../table.rkt"  "../evaluator.rkt" "../equal.rkt" "../cosette.rkt")

;; symbolic table t1 with 3 columns and 1 row
(define st1 (Table "t1" (list "J1" "G1" "S1") (gen-sym-schema 3 1)))

;; symbolic table t1 with 2 columns and 1 row
(define st2 (Table "t2" (list "J2" "G2") (gen-sym-schema 2 1)))

(define t1 st1)
(define t2 st2)


;; Select G1, G2, Sum(S1)
;; From (Selct J1 G1 S1 J2 G2
;;       From t1 Join t2
;;       Where J1 = J2)
;; Group By G1, G2
(define q1s
  (SELECT-GROUP-SUBQ
    (AS (SELECT 
          (VALS "t3.J1" "t3.G1" "t3.S1" "t3.J2" "t3.G2")
          FROM (AS (JOIN (NAMED t1) (NAMED t2)) ["t3" (list "J1" "G1" "S1" "J2" "G2")])
          WHERE (BINOP "t3.J1" = "t3.J2")) ["t3" '("J1" "G1" "S1" "J2" "G2")])
    '("t3.G1" "t3.G2")
    aggr-sum
    "t3.S1"))


;; Select G1, G2, Sum(S1)
;; From (Selct J1 G1 S1 J2 G2
;;       From t1 Join t2
;;       Where J1 >= J2)
;; Group By G1, G2
(define q2s
  (SELECT-GROUP-SUBQ
    (AS (SELECT 
          (VALS "t3.J1" "t3.G1" "t3.S1" "t3.J2" "t3.G2")
          FROM (AS (JOIN (NAMED t1) (NAMED t2)) ["t3" (list "J1" "G1" "S1" "J2" "G2")])
          WHERE (BINOP "t3.J1" >= "t3.J2")) ["t3" '("J1" "G1" "S1" "J2" "G2")])
    '("t3.G1" "t3.G2")
    aggr-sum
    "t3.S1"))



;; verify whether q1s and q2s are equal (expected to be unequal)
;; cosette will return a symbolic input to indicate that 
(let* ([model (verify (same q1s q2s))]
       [concrete-t1 (clean-ret-table (evaluate t1 model))]
       [concrete-t2 (clean-ret-table (evaluate t2 model))])
  ;; print the distinguishing input cosette find
  (println concrete-t1)
  (println concrete-t2)
)


;; the results are as follow
; (Table "t1" '("J1" "G1" "S1") '(((-2 0 3) . 7)))
;; This is a table with 7 rows of the tuple (-2 0 3), 7 here means repeats
; J1 | G1 | S1 
;----|----|---
; -2 | 0  | 3
; -2 | 0  | 3
; -2 | 0  | 3
; -2 | 0  | 3
; -2 | 0  | 3
; -2 | 0  | 3
; -2 | 0  | 3
; (Table "t2" '("J2" "G2") '(((-8 0) . 11)))

