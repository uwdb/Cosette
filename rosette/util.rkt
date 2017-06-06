#lang rosette

(require "table.rkt" "equal.rkt" "sql.rkt" "evaluator.rkt")
(require json)

(provide gen-sym-schema ;; generate a symbolic table based on schema
         gen-pos-sym-schema ;; generate table that contains only positive symbolic values
         assert-table-non-empty ;; assert that a table is not empty
         assert-table-ordered ;; assert that the table is ordered
         assert-table-col-distinct ;; assert that all values in a column is distinct from each other
         same ;; assert two queries are the same 
         neq) ;; assert two queries are not the same

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

; breaking symmetry of a table
(define (assert-table-ordered table)
  (assert (table-content-ascending? (get-content table))))

; filter all zero mul. tuples. input type is table content.
(define (filter-zero table)
  (filter (lambda (r) (not (eq? (cdr r) 0))) table))

; assert that all element in a column is distinct, it enforces that all multiplicity set to 1
; col-nums: a list of column indices
(define (assert-table-col-distinct table col-nums)
  (let ([ftable (filter-zero (get-content table))])
    (assert 
     (and (list-distinct? (map (lambda (r) (map (lambda (x) (list-ref (car r) x)) col-nums))
                               ftable))
          (foldl && #t (map (lambda (r) (and (eq? (cdr r) 0) (eq? (cdr r) 1))) ftable))))))

;; assertions

(define (same q1 q2)
  (assert (bag-equal (get-content (run q1)) (get-content (run q2)))))

(define (neq q1 q2)
  (assert (not (bag-equal (get-content (run q1)) (get-content (run q2))))))

