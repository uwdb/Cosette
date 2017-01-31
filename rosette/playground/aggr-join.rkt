#lang rosette

(require "../util.rkt" "../sql.rkt" "../table.rkt"  "../evaluator.rkt" "../equal.rkt")

; (define t1 (Table "t1" (list "c1" "c2" "c3") (gen-sym-schema 3 3)))
; (define ta (Table "R" (list "A" "B") concrete-table-2-col))
; (define tb (Table "S" (list "C" "D") concrete-table-2-col))

(define st1 (Table "t1" (list "J1" "G1" "S1") (gen-sym-schema 3 2)))
(define st2 (Table "t2" (list "J2" "G2") (gen-sym-schema 2 2)))

(define ct1 (Table "t1" (list "J1" "G1" "S1") 
                   (list (cons (list 0 0 1) 8)
                         (cons (list 0 0 1) 9)
                         (cons (list 2 2 2) 15))))

(define ct2 (Table "t2" (list "J2" "G2") 
                   (list (cons (list 0 3) 1)
                         (cons (list 2 1) 1)
                         (cons (list 2 3) 2))))

(define t1 ct1)
(define t2 ct2)
;(define t1 st1)
;(define t2 st2)

(define q1-1 
  (AS (SELECT (VALS "t3.J1" "t3.G1" "t3.S1" "t3.J2" "t3.G2")
              FROM (AS (JOIN (NAMED ct1) (NAMED ct2)) ["t3" (list "J1" "G1" "S1" "J2" "G2")])
              WHERE (BINOP "t3.J1" = "t3.J2")) ["t3" '("J1" "G1" "S1" "J2" "G2")]))

(define q2-1
  (SELECT-GROUP (NAMED t1) (list "t1.G1" "t1.J1") aggr-sum "t1.S1" ))

(run q1-1)
(run q2-1)

; commutativity of selection query 1

; commutativity of selection query 2

;(time (verify (same subq-aggr-1 subq-aggr-2)))

