#lang rosette

(require "syntax.rkt" "denotation.rkt" "table.rkt" "evaluator.rkt")

(provide (all-defined-out))

;; the interface to run sql, 
;; note that ns is the namespace defined in denotation
(define (run q)
  (denote-and-run q))

;; easy syntax rules to write sql queries
(define-syntax-rule
  (SELECT v FROM q WHERE f)
  (query-select v q f))

;; q: the table/subquery to group
;; f: group by fields
;; aggr: aggregation functions
;; target: group by field
(define-syntax-rule
  (SELECT-GROUP q gb-fields aggrf target)
  (query-aggr q gb-fields aggrf target))

;; group by but with an alternative implementation
(define-syntax-rule
  (SELECT-GROUP-SUBQ q gb-fields aggrf target)
  (SELECT-DISTINCT 
    (append (map (lambda (x) (VAL x)) gb-fields)
            (list (VAL (AGGR aggrf (SELECT 
                                     (VALS (string-append "tmp." target))
                                     FROM (AS (SELECT (append (map (lambda (x) (VAL x)) gb-fields) (list (VAL target))) FROM q WHERE (F-EMPTY)) 
                                              ["tmp" (append gb-fields (list target))])
                                     WHERE (foldl (lambda (x y) (AND x y)) (F-EMPTY) 
                                                  (map (lambda (z) (BINOP z = (string-append "tmp." z))) gb-fields)))))))
    FROM q
    WHERE (F-EMPTY)))

(define-syntax-rule
  (SELECT-DISTINCT v FROM q WHERE f)
  (query-select-distinct v q f))

(define-syntax-rule
  (UNION-ALL q1 q2)
  (query-union-all q1 q2))

(define-syntax-rule
  (JOIN q1 q2)
  (query-join q1 q2))

(define-syntax-rule (NAMED t)
                    (query-named t))

; rename the result of q with name t, and fields l (a list of string)
;(define-syntax-rule (AS q [t l])
;                    (query-rename q t l))

(define-syntax AS
  (syntax-rules 
    ()
    [(AS q [t l]) (query-rename-full q t l)]
    [(AS q [t]) (query-rename q t)]))

(define-syntax-rule
  (RENAME t name)
  (rename-table t name))

(define-syntax-rule (VAL v)
                    (cond
                      [(equal? v sqlnull) (val-const sqlnull)]
                      [(string? v) (val-column-ref v)]
                      [(int? v) (val-const v)]
                      [(val-agg? v) v]
                      [(val-bexpr? v) v]
                      [(val-uexpr? v) v]))

(define-syntax-rule (VAL-BINOP v1 op v2)
                    (val-bexpr (VAL v1) op (VAL v2)))

(define-syntax-rule (VAL-UNOP op val)
                    (val-uexpr op (VAL val)))

(define (VALS . v)
  (map (lambda (x) (VAL x)) v))

(define-syntax-rule (AGGR aggr-fun q)
                    (val-agg aggr-fun q))

(define-syntax-rule (BINOP v1 op v2)
                    (filter-binop op (VAL v1) (VAL v2)))

(define-syntax-rule (EXISTS q)
                    (filter-exists q))

(define-syntax-rule (F-EMPTY) (filter-empty))

; f can be uninterpreted functions
; f should be of type int->int->...->int->bool
(define (NARY-OP f . args)
  (filter-nary-op f (map (lambda (x) (VAL x)) args)))

(define-syntax-rule (AND f1 f2)
                    (filter-conj f1 f2))

(define-syntax-rule (NOT f)
                    (filter-not f))

(define-syntax-rule (LEFT-OUTER-JOIN q1 q2 k1 k2)
                    (query-left-outer-join q1 q2 k1 k2))

(define-syntax-rule (LEFT-OUTER-JOIN-2 q1 q2 join-query)
                    (query-left-outer-join-2 q1 q2 join-query))

(define-syntax-rule (UNIT) unit-table)

;; UNIT table is a table with 1 row and empty schema
(define unit-table
  (Table "UNIT" (list)
         (list (cons (list) 1))))

;; aggregation functions
;; input to these functions:
;;    [(v1 . m1), (v2 . m2), ..., (vn . mn)]
;; output is the aggregation result of the list

(define (aggr-count l)
  (foldl + 0 (map cdr l)))

(define (aggr-sum l)
  (foldl + 0 (map (lambda (x) (* (car x) (cdr x))) l)))

(define (aggr-max l)
  (max (map (lambda (x) (car x)) l)))

(define (aggr-min l)
  (min (map (lambda (x) (car x)) l)))

(define test-table1
  (list
    (cons (list 1 1 2) 2)
    (cons (list 1 1 2) 2)
    (cons (list 0 1 2) 2)
    (cons (list 1 2 1) 1)
    (cons (list 1 2 3) 1)
    (cons (list 2 1 0) 3)))
(define table1 (Table "t1" (list "c1" "c2" "c3") test-table1))

(define q (query-select 
            (list (val-column-ref "t1.c1") (val-column-ref "t1.c2"))
            (query-named table1)
            (filter-binop < (val-column-ref "t1.c1") (val-column-ref "t1.c2"))))

(define q2 (query-rename-full (query-named table1) "qt" (list "c12" "c22" "c32")))

(define q3 (query-join (query-named table1) (query-rename-full (query-named table1) "t2" (list "c1" "c2" "c3"))))

(define part-of-q3 (query-rename-full (query-named table1) "t2" (list "c1" "c2" "c3")))
