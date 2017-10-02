#lang rosette

(require "table.rkt")

(provide (all-defined-out))

;;; query structure

; select-args : a list of values
; from-queries : a list of tables/subqueries
; where-filter : a filter
(struct query-select (select-args from-query where-filter) #:transparent)
(struct query-select-distinct (select-args from-query where-filter) #:transparent)
(struct query-join (query1 query2) #:transparent)
(struct query-named (table-ref) #:transparent)
(struct query-rename (query table-name) #:transparent)
(struct query-rename-full (query table-name column-names) #:transparent)
(struct query-left-outer-join (query1 query2 key1 key2) #:transparent)
(struct query-left-outer-join-2 (query1 query2 join-result) #:transparent)
(struct query-union-all (query1 query2))
(struct query-aggr (query aggr-fields aggr-fun target) #:transparent)
(struct query-aggr-general (query gb-fields select-args having-filter) #:transparent)

;;; special val representing aggregation
;;; ones with aggr-function means performing aggregation
(struct val-aggr-target (aggr-func val) #:transparent)
(struct val-aggr-group-col (column-name) #:transparent)

;;; values
(struct val-const (val) #:transparent)
(struct val-column-ref (column-name) #:transparent)
(struct val-agg (agg-func query) #:transparent)
(struct val-bexpr (binop v1 v2) #:transparent)
(struct val-uexpr (op val) #:transparent)

;;; filters
(struct filter-binop (op val1 val2) #:transparent)
(struct filter-conj (f1 f2) #:transparent)
(struct filter-disj (f1 f2) #:transparent)
(struct filter-not (f1) #:transparent)
(struct filter-exists (query) #:transparent)
(struct filter-true () #:transparent)
(struct filter-false () #:transparent)
(struct filter-nary-op (f args) #:transparent) ; n-ary-operator
