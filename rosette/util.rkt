#lang rosette

(require "table.rkt" "equal.rkt" "sql.rkt" "evaluator.rkt")
(require json)

(provide gen-sym-schema
         gen-pos-sym-schema
         assert-table-non-empty
         assert-table-ordered
         same
         neq)

; generate a symbolic value
(define (gen-sv)
  (define-symbolic* sv integer?)
  sv)

; generate a tuple, n is the number of column
(define (gen-sv-row n)
  (build-list n (lambda (x) (gen-sv))))

; generate a positive symbolic value, used to represent cardinalities of tuples
(define (gen-pos-sv)
  (define-symbolic* sv-pos integer?)
  (assert (>= sv-pos 0))
  sv-pos)

; generate a positive tuple, n is the number of column
(define (gen-pos-sv-row n)
  (build-list n (lambda (x) (gen-pos-sv))))

; generate a symbolic table of num-col columns and num-row rows
(define (gen-sym-schema num-col num-row)
  (let ([gen-row (lambda (x)
                   (cons (gen-sv-row num-col)
                         (gen-pos-sv)))])
    (build-list num-row gen-row)))

; generate a symbolic table of num-col columns and num-row rows
(define (gen-pos-sym-schema num-col num-row)
  (let ([gen-row (lambda (x)
                   (cons (gen-pos-sv-row num-col)
                         (gen-pos-sv)))])
    (build-list num-row gen-row)))

; an assertion for table content non-empty
; input type is Table (instead of table content)
(define (assert-table-non-empty table)
  (assert (not (table-content-empty? (get-content table)))))

(define (assert-table-ordered table)
  (assert (table-content-ascending? (get-content table))))
;; assertions

(define (same q1 q2)
  (assert (bag-equal (get-content (run q1)) (get-content (run q2)))))

(define (neq q1 q2)
  (assert (not (bag-equal (get-content (run q1)) (get-content (run q2))))))

