#lang rosette

(require "table.rkt" "equal.rkt" "sql.rkt" "evaluator.rkt")
(require json)

(provide gen-sym-schema ;; generate a symbolic table based on schema
         gen-pos-sym-schema ;; generate table that contains only positive symbolic values
         assert-table-non-empty ;; assert that a table is not empty
         assert-table-ordered ;; assert that the table is ordered
         assert-table-cols-distinct ;; assert that all values in a list of columns is distinct from each other
         table-cols-distinct? ;; check the projection of certern cols of a table is distinct or not
         list-subset? ;; check whether the set of elements of a list is a subset of the set of elements of another list
         foreign-key-constraint? ;; check whether two tables and specified cols conform pk-fk constraint
         filter-zero
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

; list subset: whether all elements in list a are contained in b 
(define (list-subset? a b)
  (cond
    [(empty? a) #t]
    [else (if (not (member (car a) b)) #f (list-subset? (cdr a) b))]))

; filter all zero mul. tuples. input type is table content.
(define (filter-zero table)
  (filter (lambda (r) (not (eq? (cdr r) 0))) table))

; project table-content according to indices, only projecting tuple (no cardinality attached)
(define (project-content table-content indices)
  (map (lambda (r) (map (lambda (x) (list-ref (car r) x)) indices))
                               table-content))

; check that all element in a list of columns is distinct, it enforces that all multiplicity set to 1
; col-nums: a list of column indices
(define (assert-table-cols-distinct table col-nums)
  (assert (table-cols-distinct? table col-nums)))

(define (table-cols-distinct? table col-indices)
  (let ([ftable (filter-zero (get-content table))])
    (or
     (empty? col-indices)
     (and (list-distinct? (project-content ftable col-indices))
          (foldl && #t (map (lambda (r) (eq? (cdr r) 1)) ftable))))))

; primary key foreign key constraints
(define (foreign-key-constraint? pk-table fk-table pk-indices fk-indices)
  (let* ([pk-content (filter-zero (get-content pk-table))]
         [fk-content (filter-zero (get-content fk-table))]
         [pk-proj (project-content pk-content pk-indices)]
         [fk-proj (project-content fk-content fk-indices)])
  (and (table-cols-distinct? pk-table pk-indices) ; pk need to be a key first
       (list-subset? fk-proj pk-proj) ; check containment
       )))

;; assertions

(define (same q1 q2)
  (assert (bag-equal (get-content (run q1)) (get-content (run q2)))))

(define (neq q1 q2)
  (assert (not (bag-equal (get-content (run q1)) (get-content (run q2))))))

