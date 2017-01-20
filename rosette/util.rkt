#lang rosette

(require "table.rkt" "equal.rkt" "sql.rkt")
(require json)

(provide (all-defined-out))  

;; assertions

(define (same q1 q2)
    (assert (bag-equal (get-content (run q1)) (get-content (run q2)))))

(define (neq q1 q2)
  (assert (not (bag-equal (get-content (run q1)) (get-content (run q2))))))

;; aggregation functions

(define (aggr-count l)
  (foldl + 0 (map cdr (get-content l))))

(define (aggr-sum l)
  (foldl + 0 (map (lambda (x) (* (car (car x)) (cdr x)))
       (get-content l))))
