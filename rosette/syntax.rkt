#lang rosette

(require "table.rkt" "evaluator.rkt")

(provide (all-defined-out))

;;; query structure

; select-args : a list of values
; from-queries : a list of tables/subqueries
; where-filter : a filter
(struct query-select (select-args from-query where-filter) #:transparent)
(struct query-select-distinct (select-args from-query where-filter) #:transparent)
(struct query-join (query1 query2) #:transparent)
(struct query-named (table-ref) #:transparent)
(struct query-rename (query table-name column-names) #:transparent)
(struct query-left-outer-join (query1 query2 key1 key2) #:transparent)
(struct query-left-outer-join-2 (query1 query2 join-result) #:transparent)
(struct query-union-all (query1 query2))
(struct query-aggr (query aggr-fields aggr-fun target) #:transparent)

;;; values
(struct val-const (val) #:transparent)
(struct val-column-ref (column-name) #:transparent)
(struct val-agg (agg-func query) #:transparent)

;;; filters
(struct filter-binop (op val1 val2) #:transparent)
(struct filter-conj (f1 f2) #:transparent)
(struct filter-disj (f1 f2) #:transparent)
(struct filter-not (f1) #:transparent)
(struct filter-exists (query) #:transparent)
(struct filter-empty () #:transparent)

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

;; easy syntax rules to write sql queries

(define-syntax-rule
  (SELECT v FROM q WHERE f)
  (query-select v q f))

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

(define-syntax-rule (AS q [t l])
                    (query-rename q t l))

(define (RENAME t name)
  (rename-table t name))

(define (VAL v)
  (cond
    [(equal? v sqlnull) (val-const sqlnull)]
    [(string? v) (val-column-ref v)]
    [(int? v) (val-const v)]
    [(val-agg? v) v]))

(define (VALS . v)
  (map (lambda (x) (VAL x)) v))

(define (AGGR aggr-fun q)
  (val-agg aggr-fun q))

(define (BINOP v1 op v2)
  (filter-binop op (VAL v1) (VAL v2)))

(define-syntax-rule (EXISTS q)
                    (filter-exists q))

(define (AND f1 f2)
  (filter-conj f1 f2))

(define (NOT f)
  (filter-not f))

(define (LEFT-OUTER-JOIN q1 q2 k1 k2)
  (query-left-outer-join q1 q2 k1 k2))

(define (LEFT-OUTER-JOIN-2 q1 q2 join-query)
  (query-left-outer-join-2 q1 q2 join-query))
