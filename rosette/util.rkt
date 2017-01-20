#lang rosette

(require "table.rkt" "equal.rkt" "sql.rkt")
(require json)

(provide (all-defined-out))  

;; assertions

(define (same q1 q2)
    (assert (bag-equal (get-content (run q1)) (get-content (run q2)))))

(define (neq q1 q2)
  (assert (not (bag-equal (get-content (run q1)) (get-content (run q2))))))

