#lang rosette

(require "symmetry.rkt" "table.rkt" "equal.rkt" "syntax.rkt" "sql.rkt" "evaluator.rkt")
(require json)

(provide gen-sym-schema ;; generate a symbolic table based on schema
         gen-qex-sym-schema ;; generate a symbolic table based on qex schema
         gen-pos-sym-schema ;; generate table that contains only positive symbolic values
         prop-table-empty
         prop-table-non-empty
         prop-table-ordered
         prop-table-col-distinct
         assert-table-mconstr ;; assert using mconstr
         assert-table-non-empty ;; assert that a table is not empty
         assert-table-ordered ;; assert that the table is ordered
         assert-table-col-distinct ;; assert that all values in a column is distinct from each other
         same ;; assert two queries are the same 
         neq ;; assert two queries are not the same
         ) 

;;;;; Symbolic utilities

; generate a symbolic value
(define (gen-sv)
  (define-symbolic* sv integer?)
  sv)

; generate a positive symbolic value, used to represent cardinalities of tuples
(define (gen-non-neg-sv)
  (define-symbolic* sv-non-neg integer?)
  (assert (>= sv-non-neg 0))
  sv-non-neg)

; generate a positive symbolic value, used to represent cardinalities of tuples
(define (gen-pos-sv)
  (define-symbolic* sv-pos integer?)
  (assert (> sv-pos 0))
  sv-pos)

; generate a positive symbolic value, used to represent cardinalities of tuples
(define (gen-0-1-sv)
  (define-symbolic* sv integer?)
  (assert (or (= sv 0) (= sv 1)))
  sv)

; generate a tuple, n is the number of column
(define (gen-sv-list n)
  (build-list n (lambda (x) (gen-sv))))

; generate a positive tuple, n is the number of column
(define (gen-non-neg-sv-list n)
  (build-list n (lambda (x) (gen-non-neg-sv))))

;;;;; table utils

; generate a symbolic table of num-col columns and num-row rows
(define (gen-sym-schema num-col num-row)
  ; generating symbolic table row by row
  (let* ([gen-row (lambda (x) (cons (gen-sv-list num-col) (gen-non-neg-sv)))]
         [table (build-list num-row gen-row)])
    (assert (table-content-non-desc? table))
    table))

; generate a symbolic table of num-col columns and num-row rows
(define (gen-pos-sym-schema num-col num-row)
  (let ([gen-row (lambda (x) (cons (gen-non-neg-sv-list num-col) (gen-non-neg-sv)))])
    (build-list num-row gen-row)))

; generate a symbolic table of num-col columns and num-row rows
(define (gen-qex-sym-schema num-col num-row)
  (let* ([gen-row (lambda (x) (cons (gen-sv-list num-col) 1))]
         [table (build-list num-row gen-row)])
    (assert (table-content-non-desc? table))
    table))

(define (subst-mconstr v sv-base sv-current)
  ;; sv-base is a hashtable that maps values to symbolic 
  (cond
    [(c-primitive? v)
     `(,(c-primitive-op v)
       ,(subst-mconstr (c-primitive-left v) sv-base sv-current) 
       ,(subst-mconstr (c-primitive-right v) sv-base sv-current))]
    [(c-true? v) #t]
    [(c-false? v) #f]
    [(c-conj? v)
     (let ([content (map (lambda (x) (subst-mconstr  x sv-base sv-current)) 
                         (c-conj-preds v))])
       (cond [(eq? (length content) 0) #t]
             [(eq? (length content) 1) (car content)]
             [else (foldl (lambda (x y) `(and ,x ,y)) (car content) (cdr content))]))]
    [(c-disj? v) 
     (let ([content (map (lambda (x) (subst-mconstr  x sv-base sv-current)) 
                         (c-disj-preds v))])
       (cond [(eq? (length content) 0) #t]
             [(eq? (length content) 1) (car content)]
             [else (foldl (lambda (x y) `(or ,x ,y)) (car content) (cdr content))]))]
    [(v-const? v) (v-const-c v)]
    [(v-uexpr? v) `(,(v-uexpr-op v) ,(subst-mconstr (v-uexpr-v v) sv-base sv-current))]
    [(v-bexpr? v) 
     `(,(v-bexpr-op v)
       ,(subst-mconstr (v-bexpr-v1 v) sv-base sv-current) 
       ,(subst-mconstr (v-bexpr-v2 v) sv-base sv-current))]
    [(v-ref? v) (list-ref sv-current (v-ref-id v))]
    [(v-symval? v) 
     (hash-ref! sv-base (v-symval-id v) (gen-sv))]
    [else v]))

; the namespace used to evaluate constraint
(define-namespace-anchor anc)
(define ns (namespace-anchor->namespace anc))

(define (assert-table-mconstr table mconstr)
   (if (null? mconstr) 
       '()
       (let* ([optimized-mconstr (remove-unused-constr mconstr)]
              [content (Table-content table)]
              [base (make-hash)]
              [cs (foldl (lambda (x y) `(and ,x ,y)) #t
                         (map (lambda (x) (subst-mconstr optimized-mconstr base (car x))) content))])
         (assert (eval cs ns)))))

; an assertion for table content non-empty
; input type is Table (instead of table content)
(define (prop-table-empty table) (table-content-empty? (get-content table)))
(define (prop-table-non-empty table) (not (prop-table-empty table)))
; breaking symmetry of a table
(define (prop-table-ordered table) (table-content-non-desc? (get-content table)))
; assert that all element in a column is distinct, it enforces that all multiplicity set to 1
(define (prop-table-col-distinct table col-num) 
  (and (list-distinct? (map (lambda (r) (list-ref (car r) col-num)) (get-content table)))
       (foldl && #t (map (lambda (r) (and (eq? (cdr r) 0) (eq? (cdr r) 1))) (get-content table)))))

(define (assert-table-non-empty table) (assert (prop-table-non-empty table)))
(define (assert-table-ordered table) (assert (prop-table-ordered table)))
(define (assert-table-col-distinct table col-num) (assert (prop-table-col-distinct table col-num)))

;; assertions
(define (same q1 q2)
  (assert (bag-equal (get-content (run q1)) (get-content (run q2)))))

(define (neq q1 q2)
  (assert (not (bag-equal (get-content (run q1)) (get-content (run q2))))))

