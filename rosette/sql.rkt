#lang rosette

(require "syntax.rkt" "denotation.rkt" "table.rkt" "evaluator.rkt")

(provide (all-defined-out))

;; the interface to run sql, 
;; note that ns is the namespace defined in denotation
(define (run q) (denote-and-run q))

;;;;;;;;; query level syntax macros ;;;;;;;;;;;;

;; easy syntax rules to write sql queries
(define-syntax SELECT 
  (syntax-rules () [(SELECT v FROM q WHERE f) (query-select v q f)]
                   [(SELECT v FROM q WHERE f GROUP-BY g HAVING h) (query-aggr-general q f g v h)]))

(define-syntax-rule (SELECT-DISTINCT v FROM q WHERE f) (query-select-distinct v q f))
;; group by syntax, values in v can refer to aggregation values

(define-syntax-rule (UNION-ALL q1 q2) (query-union-all q1 q2))
(define-syntax-rule (TABLE-UNION-ALL t1 t2) (union-all t1 t2))
(define-syntax-rule (JOIN q1 q2) (query-join q1 q2))
(define-syntax-rule (NAMED t) (query-named t))
(define-syntax-rule (RENAME t name) (rename-table t name))
(define-syntax-rule (LEFT-OUTER-JOIN q1 q2 p) (query-left-outer-join q1 q2 p))
(define-syntax-rule (LEFT-OUTER-JOIN-1 q1 q2 k1 k2) (query-left-outer-join-1 q1 q2 k1 k2))

(define-syntax AS
  (syntax-rules () [(AS q [t l]) (query-rename-full q t l)]
                   [(AS q [t]) (query-rename q t)]))

;; UNIT table is a table with 1 row and empty schema
(define unit-table (Table "UNIT" (list) (list (cons (list) 1))))
(define-syntax-rule (UNIT) unit-table)

;; q: the table/subquery to group
;; f: group by fields
;; aggr: aggregation functions
;; target: group by field

; old implementation
;(define-syntax-rule (SELECT-GROUP q gb-fields aggrf target) (query-aggr q gb-fields aggrf target))

; denote to the new interface
(define-syntax-rule (SELECT-GROUP q gb-fields aggrf target) 
                    (SELECT (append (map (lambda (x) (val-column-ref x)) gb-fields) 
                                    (list (val-uexpr aggrf (VAL target)))) 
                     FROM q 
                     WHERE (TRUE)
                     GROUP-BY gb-fields
                     HAVING (TRUE)))

;; group by but with an alternative implementation
(define-syntax-rule
  (SELECT-GROUP-SUBQ q gb-fields aggrf target)
  (SELECT-DISTINCT 
    (append (map (lambda (x) (VAL x)) gb-fields)
            (list (VAL (AGGR-SUBQ aggrf (SELECT 
                                          (VALS (string-append "tmp." target))
                                          FROM (AS (SELECT (append (map (lambda (x) (VAL x)) gb-fields) (list (VAL target))) FROM q WHERE (TRUE)) 
                                                   ["tmp" (append gb-fields (list target))])
                                          WHERE (foldl (lambda (x y) (AND x y)) (TRUE) 
                                                       (map (lambda (z) (BINOP z = (string-append "tmp." z))) gb-fields)))))))
    FROM q
    WHERE (TRUE)))

;;;;;;;;;;;;;;;;;;; value-level syntax macros ;;;;;;;;;;;;;;;;;;;

(define-syntax-rule (VAL v)
                    (cond
                      [(equal? v sqlnull) (val-const sqlnull)]
                      [(string? v) (val-column-ref v)]
                      [(int? v) (val-const v)]
                      [else v]))

(define-syntax-rule (VAL-BINOP v1 op v2) (val-bexpr op (VAL v1) (VAL v2)))
(define-syntax-rule (VAL-UNOP op val) (val-uexpr op (VAL val)))
(define-syntax-rule (AGGR-SUBQ aggr-fun q) (val-aggr-subq aggr-fun q))
(define (VALS . v) (map (lambda (x) (VAL x)) v))

;;;;;;;;;;;;;;;;;; filter-level syntax macros ;;;;;;;;;;;;;;;;;;;

(define-syntax-rule (EXISTS q) (filter-exists q))
(define-syntax-rule (TRUE) (filter-true))
(define-syntax-rule (FALSE) (filter-false))

; f can be uninterpreted functions
; f should be of type int->int->...->int->bool
(define (NARY-OP f . args) (filter-nary-op f (map (lambda (x) (VAL x)) args)))

(define-syntax-rule (BINOP v1 op v2) (filter-binop op (VAL v1) (VAL v2)))
(define-syntax-rule (OR f1 f2) (filter-disj f1 f2))
(define-syntax-rule (AND f1 f2) (filter-conj f1 f2))
(define-syntax-rule (NOT f) (filter-not f))
