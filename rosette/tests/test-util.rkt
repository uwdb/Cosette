#lang rosette

(require "../util.rkt" "../syntax.rkt" "../denotation.rkt" 
         "../table.rkt"  "../evaluator.rkt" "../equal.rkt")

(provide neq same concrete-table-3-col concrete-table-2-col num-rows-in-sym-table)

(define num-rows-in-sym-table 3)

(define (same q1 q2)
    (assert (bag-equal (get-content (run q1)) (get-content (run q2)))))

(define (neq q1 q2)
  (assert (not (bag-equal (get-content (run q1)) (get-content (run q2))))))

(define concrete-table-3-col
    (list
      (cons (list 1 1 2) 2)
      (cons (list 0 1 2) 2)                 
      (cons (list 1 2 1) 1)
      (cons (list 2 1 0) 3)
      (cons (list 3 1 0) 2)))

(define concrete-table-2-col
    (list
      (cons (list 1 1) 2)
      (cons (list 0 2) 2)                 
      (cons (list 1 2) 1)
      (cons (list 2 1) 3)))

;(define test-table-1
;  (Table "a" (list "c1" "c2" "c3") concrete-table-3-col))

;(define test-table-2
;  (Table "b" (list "d1" "c2" "c3") concrete-table-2-col))

;(define q (LEFT-OUTER-JOIN (NAMED test-table-1) (NAMED test-table-2) 0 0))
;(print (run q))
