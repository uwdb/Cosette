#lang rosette

(require "../util.rkt" "../sql.rkt" "../table.rkt"  "../evaluator.rkt" "../equal.rkt")

; define concrete tables ct1 and ct2

(define ct1 (Table "t1" (list "J1" "G1" "S1") 
                   (list (cons (list 0 3 1) 1)
                         (cons (list 0 3 3) 3)
                         (cons (list 2 7 2) 4))))
(define ct2 (Table "t2" (list "J2" "G2") 
                   (list (cons (list 0 3) 1)
                         (cons (list 2 1) 1)
                         (cons (list 2 3) 2))))

(define t1 ct1)
(define t2 ct2)

;; Select G1, G2, Sum(S1)
;; From (Selct J1 G1 S1 J2 G2
;;       From t1 Join t2
;;       Where J1 = J2)
;; Group By G1, G2
(define q1
  (SELECT-GROUP
    (AS (SELECT 
          (VALS "t3.J1" "t3.G1" "t3.S1" "t3.J2" "t3.G2")
          FROM (AS (JOIN (NAMED t1) (NAMED t2)) ["t3" (list "J1" "G1" "S1" "J2" "G2")])
          WHERE (BINOP "t3.J1" = "t3.J2")) ["t3" (list "J1" "G1" "S1" "J2" "G2")])
    (list "t3.G1" "t3.G2")
    aggr-sum
    "t3.S1"))

;; Select G1, G2, Sum(S1)
;; From (Selct J1 G1 sumS1 J2 G2
;;       From (Select J1, G2, Sum(S1) As sumS1 
;;             From t1 
;;             Group By J1, G1) Join t2
;;       Where J1 = J2)
;; Group By G1, G2
(define q2
  (SELECT-GROUP
    (AS (SELECT 
          (VALS "t3.J1" "t3.G1" "t3.Sum1" "t3.J2" "t3.G2")
          FROM (AS (JOIN (SELECT-GROUP (NAMED t1) (list "t1.J1" "t1.G1") aggr-sum "t1.S1" )
                         (NAMED t2)) ["t3" (list "J1" "G1" "Sum1" "J2" "G2")])
          WHERE (BINOP "t3.J1" = "t3.J2"))
        ["t3" '("J1" "G1" "Sum1" "J2" "G2")])
    (list "t3.G1" "t3.G2")
    aggr-sum
    "t3.Sum1"))

(displayln "Output from q1:")
(displayln (run q1))

(displayln "")


(displayln "Output from q2:")
(displayln (run q2))
