#lang rosette

(require "symmetry.rkt" "table.rkt" "equal.rkt" "syntax.rkt" "sql.rkt" "evaluator.rkt")
(require json)

(provide gen-sym-schema ;; generate a symbolic table based on schema
         gen-pos-sym-schema ;; generate table that contains only positive symbolic values
         assert-table-mconstr ;; assert using mconstr
         assert-table-non-empty ;; assert that a table is not empty
         assert-table-ordered ;; assert that the table is ordered
         assert-table-col-distinct ;; assert that all values in a column is distinct from each other
         same ;; assert two queries are the same 
         neq ;; assert two queries are not the same
         always-empty ;; a query always produce empty result
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
  (let ([gen-row (lambda (x) (cons (gen-sv-list num-col) (gen-non-neg-sv)))])
    (build-list num-row gen-row)))

; generate a symbolic table of num-col columns and num-row rows
(define (gen-pos-sym-schema num-col num-row)
  (let ([gen-row (lambda (x) (cons (gen-non-neg-sv-list num-col) (gen-non-neg-sv)))])
    (build-list num-row gen-row)))

; generate a symbolic table of num-col columns and num-row rows
(define (gen-qex-sym-schema num-col num-row)
  (let* ([gen-row (lambda (x) (cons (gen-sv-list num-col) 1))]
         [table (build-list num-row gen-row)])
    (assert (table-content-ascending? table))
    table))

(define (subst-mconstr v sv-base sv-current)
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
    [(v-symval? v) (list-ref sv-base (v-symval-id v))]
    [else v]))

; the namespace used to evaluate constraint
(define-namespace-anchor anc)
(define ns (namespace-anchor->namespace anc))

(define (assert-table-mconstr table mconstr)
   (if (null? mconstr) 
       '()
       (let* ([content (Table-content table)]
              [base (car (car content))]
              [cs (foldl (lambda (x y) `(and ,x ,y)) #t 
                         (map (lambda (x) (subst-mconstr mconstr base (car x))) content))])
         (assert (eval cs ns)))))

; generate constraints and assertions from meta constraints 
(define (gen-sym-schema-mconstr num-col num-row mconstr)
  (if (or (eq? num-row 0) (null? mconstr)) 
      (list)
      (let* ([sym-table 
              (build-list 
                num-row 
                (lambda (x)
                  (cons (gen-sv-list num-col) (gen-non-neg-sv))))]
              [base (car (car sym-table))]
              [cs (foldl (lambda (x y) `(and ,x ,y)) #t 
                         (map (lambda (x) (subst-mconstr mconstr base (car x))) sym-table))])
        (assert (eval cs ns))
        sym-table)))

; an assertion for table content non-empty
; input type is Table (instead of table content)
(define (assert-table-non-empty table)
  (assert (not (table-content-empty? (get-content table)))))

; breaking symmetry of a table
(define (assert-table-ordered table)
  (assert (table-content-ascending? (get-content table))))

; assert that all element in a column is distinct, it enforces that all multiplicity set to 1
(define (assert-table-col-distinct table col-num)
  (assert 
    (and (list-distinct? (map (lambda (r) (list-ref (car r) col-num)) (get-content table)))
         (foldl && #t (map (lambda (r) (and (eq? (cdr r) 0) (eq? (cdr r) 1))) (get-content table))))))

;; assertions
(define (same q1 q2)
  (assert (bag-equal (get-content (run q1)) (get-content (run q2)))))

(define (neq q1 q2)
  (assert (not (bag-equal (get-content (run q1)) (get-content (run q2))))))

(define (always-empty q)
  (assert (table-content-empty? (get-content (run q)))))
