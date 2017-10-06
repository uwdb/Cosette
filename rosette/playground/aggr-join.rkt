#lang rosette

(require "../util.rkt" "../sql.rkt" "../table.rkt"  "../evaluator.rkt" "../equal.rkt")

; (define t1 (Table "t1" (list "c1" "c2" "c3") (gen-sym-schema 3 3)))
; (define ta (Table "R" (list "A" "B") concrete-table-2-col))
; (define tb (Table "S" (list "C" "D") concrete-table-2-col))

(define st1 (Table "t1" (list "J1" "G1" "S1") (gen-sym-schema 3 1)))
(define st2 (Table "t2" (list "J2" "G2") (gen-sym-schema 2 1)))

(define ct1 (Table "t1" (list "J1" "G1" "S1") 
                   (list (cons (list 0 3 1) 1)
                         (cons (list 0 3 3) 3)
                         (cons (list 2 7 2) 4))))
(define ct2 (Table "t2" (list "J2" "G2") 
                   (list (cons (list 0 3) 1)
                         (cons (list 2 1) 1)
                         (cons (list 2 3) 2))))

(define ct21 (Table "t1" (list "J1" "G1" "S1") 
                   (list (cons (list 0 0 0) 0))))
(define ct22 (Table "t2" (list "J2" "G2") 
                   (list (cons (list 0 0) 0))))
(define t1 ct1)
(define t2 ct2)
;(define t1 st1)
;(define t2 st2)

(define q1s
  (SELECT-GROUP-SUBQ
    (AS (SELECT 
          (VALS "t3.J1" "t3.G1" "t3.S1" "t3.J2" "t3.G2")
          FROM (AS (JOIN (NAMED t1) (NAMED t2)) ["t3" (list "J1" "G1" "S1" "J2" "G2")])
          WHERE (BINOP "t3.J1" = "t3.J2")) ["t3" '("J1" "G1" "S1" "J2" "G2")])
    '("t3.G1" "t3.G2")
    aggr-sum
    "t3.S1"))

(define q2s
  (SELECT-GROUP-SUBQ
    (AS (SELECT 
          (VALS "t3.J1" "t3.G1" "t3.Sum1" "t3.J2" "t3.G2")
          FROM (AS (JOIN (SELECT-GROUP-SUBQ (NAMED t1) (list "t1.J1" "t1.G1") aggr-sum "t1.S1" )
                         (NAMED t2)) ["t3" '("J1" "G1" "Sum1" "J2" "G2")])
          WHERE (BINOP "t3.J1" = "t3.J2"))
        ["t3" '("J1" "G1" "Sum1" "J2" "G2")])
    ;'("t3.G1" "t3.G2")
    '("t3.G1" "t3.G2")
    aggr-sum
    "t3.Sum1"))

(define q1
  (SELECT-GROUP
    (AS (SELECT 
          (VALS "t3.J1" "t3.G1" "t3.S1" "t3.J2" "t3.G2")
          FROM (AS (JOIN (NAMED t1) (NAMED t2)) ["t3" (list "J1" "G1" "S1" "J2" "G2")])
          WHERE (BINOP "t3.J1" = "t3.J2")) ["t3" '("J1" "G1" "S1" "J2" "G2")])
    '("t3.G1" "t3.G2")
    aggr-sum
    "t3.S1"))

(define q2
  (SELECT-GROUP
    (AS (SELECT 
          (VALS "t3.J1" "t3.G1" "t3.Sum1" "t3.J2" "t3.G2")
          FROM (AS (JOIN (SELECT-GROUP (NAMED t1) (list "t1.J1" "t1.G1") aggr-sum "t1.S1" )
                         (NAMED t2)) ["t3" '("J1" "G1" "Sum1" "J2" "G2")])
          WHERE (BINOP "t3.J1" = "t3.J2"))
        ["t3" '("J1" "G1" "Sum1" "J2" "G2")])
    ;'("t3.G1" "t3.G2")
    '("t3.G1" "t3.G2")
    aggr-sum
    "t3.Sum1"))

(writeln (run q1))
(writeln (run q2))

(time (verify (same q1 q2)))
(time (verify (same q1s q2s)))

