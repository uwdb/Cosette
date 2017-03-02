#lang rosette
;; denotation rules for SQL

(require "syntax.rkt" "table.rkt" "evaluator.rkt")

(provide (all-defined-out))

(define-namespace-anchor anc)
(define ns (namespace-anchor->namespace anc))

(define (denote-and-run q)
  (let ([query-in-rkt (denote-sql q (make-hash))])
;    (println query-in-rkt) ;; if we want to debug the query after denotation, uncomment this line
    ((eval query-in-rkt ns) '())))

;; query: the sql query to denote to
;; index-map: the mapping of the names to their index in the context, which is a hash map
;; result: a quasi-quated lambda calculas representing the denotation of the sql query
(define (denote-sql query index-map)
  (cond 
    ; denote named table
    [(query-named? query) 
     `(lambda (e) ,(query-named-table-ref query))]
    ; denote join to a racket program
    [(query-join? query) 
     `(lambda (e) 
        (xproduct
          (,(denote-sql (query-join-query1 query) index-map) e)
          (,(denote-sql (query-join-query2 query) index-map) e)
          "dummy"))]
    ; denote left-outer-join table
    [(query-left-outer-join? query)
     (let* 
       ([q1 `(,(denote-sql (query-left-outer-join-query1 query) index-map) e)]
        [q2 `(,(denote-sql (query-left-outer-join-query2 query) index-map) e)]
        [k1 (query-left-outer-join-key1 query)]
        [k2 (query-left-outer-join-key2 query)])
       `(lambda (e) (left-outer-join ,q1 ,q2 ,k1 ,k2)))]
    ; denote left-outer-join table
    [(query-left-outer-join-2? query)
     (let* 
       ([q1 `(,(denote-sql (query-left-outer-join-2-query1 query) index-map) e)]
        [q2 `(,(denote-sql (query-left-outer-join-2-query2 query) index-map) e)]
        [jq `(,(denote-sql (query-left-outer-join-2-join-result query) index-map) e)])
       `(lambda (e) (left-outer-join-2 ,q1 ,q2 ,jq)))]
    ; query union all
    [(query-union-all? query)
     (let* 
       ([q1 `(,(denote-sql (query-union-all-query1 query) index-map) e)]
        [q2 `(,(denote-sql (query-union-all-query2 query) index-map) e)])
       `(lambda (e) (union-all ,q1 ,q2)))]
    ; denote rename table and schema
    [(query-rename? query)
     `(lambda (e)
        (rename-table (,(denote-sql (query-rename-query query) index-map) e) ,(query-rename-table-name query)))]
    ; denote rename table full and schema
    [(query-rename-full? query)
     `(lambda (e)
        (rename-table-full (,(denote-sql (query-rename-full-query query) index-map) e) 
                           ,(query-rename-full-table-name query)
                           ;;; it is very tricky below, we need to pass down single quote ' to make the list a list to make it runnable 
                           ',(query-rename-full-column-names query)))]
    ; denote select query
    [(query-select? query)
     `(lambda (e)
        ,(let* ([table (query-select-from-query query)]
                [schema (extract-schema table)]
                [name-hash (hash-copy index-map)])
           (map (lambda (col-name idx)
                  (hash-set! name-hash col-name (+ idx (hash-count index-map))))
                schema (range (length schema)))
           (let* ([from-clause (eval (denote-sql table index-map) ns)]
                  [where-clause (eval (denote-filter
                                        (query-select-where-filter query)
                                        name-hash) ns)]
                  [from-table `(,from-clause e)]
                  [row-funcs (map (lambda (arg) (eval (denote-value arg name-hash) ns))
                                  (query-select-select-args query))]
                  [row-func-wrap (lambda (r) (map (lambda (f) (f r)) row-funcs))])
             `(let ([content (map (lambda (r) (cons (,row-func-wrap (car r)) (cdr r)))
                                  (filter (lambda (r) (,where-clause (car r)))
                                          (map (lambda (r) (cons (append e (car r)) (cdr r)))
                                               (Table-content ,from-table))))]
                    [new-name "dummy"]
                    [new-schema (,extract-schema ,query)])
                (Table new-name new-schema (dedup-accum content))))))]
    ; denote aggregation query
    [(query-aggr? query)
     (let* ([inner-q (query-aggr-query query)]
             [schema (extract-schema inner-q)]
             [name-hash (hash-copy index-map)])
        (map (lambda (col-name idx)
               (hash-set! name-hash col-name (+ idx (hash-count index-map))))
             schema (range (length schema)))
          `(lambda (e) 
             (let ([content (aggr-raw 
                              (get-content (,(denote-sql (query-aggr-query query) index-map) e)) 
                              ;;; it is very tricky below, we need to pass down single quote ' to make the list a list to make it runnable 
                              ',(map (lambda (x) (hash-ref name-hash x)) (query-aggr-aggr-fields query)) 
                              ,(query-aggr-aggr-fun query) 
                              ,(hash-ref name-hash (query-aggr-target query)))])
               (Table "dummy" ',(extract-schema query) content))))]
    ; denote select distinct query
    [(query-select-distinct? query)
     (let ([args (query-select-distinct-select-args query)]
           [from (query-select-distinct-from-query query)]
           [where (query-select-distinct-where-filter query)])
       `(lambda (e)
          (let* ([result (,(denote-sql (query-select args from where) index-map) e)]
                 [t-name (Table-name result)]
                 [t-schema (Table-schema result)]
                 [t-content (Table-content result)]
                 [dedup-result (dedup t-content)])
            (Table t-name t-schema dedup-result))))]))

;; convert schema list to hash map (name -> index)           
(define (list->hash l)
  (let ([h (make-hash)])
    (map (lambda (name idx) (hash-set! h name idx))
         l
         (range (length l)))
    h))

;; query: the sql query to extract schema for
(define (extract-schema query)
  (cond 
    [(query-named? query)
     (get-qualified-schema (query-named-table-ref query))]
    ;(map (lambda (x) (string-append (get-table-name (query-named-table-ref query)) "." x))(get-schema (query-named-table-ref query)))]
    [(query-join? query) 
     (append (extract-schema (query-join-query1 query)) 
             (extract-schema (query-join-query2 query)))]
    [(query-rename? query)
     (let ([tn (query-rename-table-name query)]
           [cnames (extract-schema (query-rename-query query))])
       (map (lambda (x) (string-append tn "." x)) cnames))]
    [(query-rename-full? query)
     (let ([tn (query-rename-full-table-name query)]
           [cnames (query-rename-full-column-names query)])
       (map (lambda (x) (string-append tn "." x)) cnames))]
    [(query-select? query)
     (map (lambda (x) "dummy") (query-select-select-args query))]
    [(query-aggr? query)
     (append (query-aggr-aggr-fields query) (list (query-aggr-target query)))]))

;;; denote value returns tuple -> value
(define (denote-value value nmap)
  (cond
    [(val-const? value) `(lambda (e) ,(val-const-val value))]
    [(val-column-ref? value)
     `(lambda (e) (list-ref e ,(hash-ref nmap (val-column-ref-column-name value))))]
    [(val-bexpr? value)
     `(lambda (e) (,(val-bexpr-binop value) (,(denote-value (val-bexpr-v1 value) nmap) e)
                                            (,(denote-value (val-bexpr-v2 value) nmap) e)))]
    [(val-uexpr? value)
     `(lambda (e) (,(val-uexpr-op value) (,(denote-value (val-uexpr-val value) nmap) e)))]
    [(val-agg? value)
     `(lambda (e) 
        (,(val-agg-agg-func value) 
          (map (lambda (r) (cons (car (car r)) (cdr r))) 
               (get-content (,(denote-sql (val-agg-query value) nmap) e)))))]))

;;; denote filters returns tuple -> bool
(define (denote-filter f nmap)
  (cond
    [(filter-binop? f)
     `(lambda (e)
        (,(filter-binop-op f)
         (,(denote-value (filter-binop-val1 f) nmap) e)
         (,(denote-value (filter-binop-val2 f) nmap) e)))]
    [(filter-conj? f)
     `(lambda (e) (and (,(denote-filter (filter-conj-f1 f) nmap) e)
                       (,(denote-filter (filter-conj-f2 f) nmap) e)))]
    [(filter-disj? f)
     `(lambda (e) (or (,(denote-filter (filter-disj-f1 f) nmap) e)
                      (,(denote-filter (filter-disj-f2 f) nmap) e)))]
    [(filter-not? f)
     `(lambda (e) (not (,(denote-filter (filter-not-f1 f) nmap) e)))]
    [(filter-exists? f)
     `(lambda (e) (if (empty? (,(denote-sql (filter-exists-query f) nmap) e)) #f #t))]
    [(filter-empty? f) `(lambda (e) #t)]
    [(filter-uf? f)
     `(lambda (e)
        (apply
         ,(filter-uf-f f)
         ,(map (lambda (x)
                 `(,(denote-value x nmap) e))
               (filter-uf-args f))))]))

;;(define test-query1
;;  (SELECT (VALS "t1.c1" "t1.c2" "t1.c3" "t2.c1" "t2.c2" "t2.c3")
;;   FROM (JOIN (NAMED table1) (AS (NAMED table1) ["t2" '("c1" "c2" "c3")]))
;;   WHERE (AND (BINOP "t1.c1" < "t2.c2") (BINOP "t1.c3" < "t2.c3"))))

;; (run test-query1)

; (rename-table ((lambda (e) (Table "t1" (list "c1" "c2" "c3") '())) '()) "t2")

; (define denotation-q3
;   '(lambda (e) (rename-table ((lambda (e) (Table "t1" (list "c1" "c2" "c3") '())) e) "t2")) )

; ((eval (denote-sql q3 '()) ns) '())

; (extract-schema q3)
; (denote-sql q (make-hash))
; ((eval (denote-sql q (make-hash)) ns) '())

