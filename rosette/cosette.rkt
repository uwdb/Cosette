; The rosette interface for cosette

#lang rosette

(require "util.rkt" "evaluator.rkt" "table.rkt" "sql.rkt" "equal.rkt" "syntax.rkt" "denotation.rkt" "symmetry.rkt")
(require racket/pretty)
(require json)

(provide cosette-sol->json 
         cosette-solve
         cosette-check-output-prop
         table-info
         solve-queries
         solve-queries-symbreak
         init-sym-tables
         init-sym-tables-from-func
         assert-sym-tables
         assert-sym-tables-mconstr
         init-table-size-list
         inc-table-size-list)

; format cosette solution into a json string
; {
;    "status": ... // "eq" or "neq"
;    "counter-example": [ 
;       {
;        "table-name": ..., // a string representing table name
;        "table-content": ...// a list of lists representing the table content, 
;                            //first list is schema
;       },
;    .....
;    ]
; }
(define (cosette-sol->json solution)
  (let ([status (car solution)]
        [tables (cdr solution)])
    (jsexpr->string 
      (hasheq 'status status
              'counter-example (map (lambda (t) (table->jsexpr t)) tables)))))

; remove symbolic values from a ret-table to make it executable
(define (clean-ret-table table)
  (let* ([name (Table-name table)]
         [schema (Table-schema table)]
         [content (Table-content table)]
         [new-content 
          (remove-zero (dedup-accum (map (lambda (r) (cons (map (lambda (v) (zero-if-symbolic v)) (car r)) 
                                                           (zero-if-symbolic (cdr r)))) 
                                         content)))])
    (Table name schema new-content)))

(define (zero-if-symbolic v)
  (cond [(term? v) 0]
        [else v])) 

(define (cosette-solve q1 q2 input-tables)
  (let ([solution (verify (same q1 q2))])
    (cond 
      [(sat? solution) 
       (let* ([tables (evaluate input-tables solution)]
              [q1t (evaluate q1 solution)]
              [q2t (evaluate q2 solution)]
              [clean-tables (map clean-ret-table tables)])
         (displayln "[Table evaluation results]")
         (displayln (format "  ~a" (clean-ret-table (denote-and-run q1t))))
         (displayln (format "  ~a" (clean-ret-table (denote-and-run q2t))))
         (cons "NEQ" clean-tables))]
      [else (cons "EQ"  (list))])))

(define (cosette-check-output-prop q input-tables sym-vals output-prop)
  (let ([solution (verify (assert (output-prop (run q))))])
    (cond 
      [(sat? solution) 
       (let* ([tables (evaluate input-tables solution)]
              [vals (evaluate sym-vals solution)]
              [qt (evaluate q solution)]
              [clean-tables (map clean-ret-table tables)])
         (displayln "[Evaluation Result]")
         (displayln (format "  ~a" vals))
         (displayln (format "  ~a" (clean-ret-table (denote-and-run qt))))
         (cons "NEQ" clean-tables))]
      [else (cons "EQ"  (list))])))

(define (table->jsexpr t) 
  (hasheq 'table-name (get-table-name t) 
          'table-content (list (get-schema t) 
                               (map (lambda (r)
                                      (list (map sv->string (car r))
                                            (sv->string (cdr r)))) 
                                    (get-content t)))))

(define (sv->string v)
  (if (term? v) (term->string v) v))

(define (term->string v)
  (let ([op (open-output-string)])
    (write v op)
    (get-output-string op)))

; note: the new interface requires rewrite all the queries to the following form

; a struct stores table name and schema
(struct table-info (name schema)
        #:transparent
        #:guard (lambda (name schema type-name)
                  (cond
                    [(not (string? name)) (error type-name "bad name:~e" name)]
                    [(not (list? schema)) (error type-name "bad schema:~e" schema)]
                    [else (values name schema)])))

; initialize the table size list
(define (init-table-size-list fq-list table-info-list)
  (let ([used-tf (used-table-info fq-list table-info-list)])
    (map (lambda (tf) (if (set-member? used-tf (table-info-name tf)) 1 0)) table-info-list)))


; given a list of table sizes, increase the size of them one at a time (zig-zag style)
(define (inc-table-size-list size-list)
  (letrec ([min-pos-val (first (sort (filter (lambda (v) (> v 0)) size-list) <))]
           [update-func 
            (lambda (l) (match l
                          [(list x) (list (+ x 1))]
                          [(cons x l) (if (eq? x min-pos-val)
                                          (append (list (+ x 1)) l)
                                          (append (list x) (update-func l)))]))])
    (update-func size-list)))

(define (init-sym-tables table-info-list table-size-list)
  ; generate a symbolic table according to table-info and size
  (define (gen-sym-table-from-info tf size)
    (let ([schema (table-info-schema tf)])
      (Table (table-info-name tf) 
             schema 
             (gen-sym-schema (length schema) size))))
  (map (lambda (i) (gen-sym-table-from-info
                     (list-ref table-info-list i)
                     (list-ref table-size-list i)))
       (build-list (length table-size-list) values)))


(define (init-sym-tables-from-func table-info-list table-size-list table-init-func)
  ; generate a symbolic table according to table-info and size as well as generation function
  (define (gen-sym-table-from-info tf size)
    (let ([schema (table-info-schema tf)])
      (Table (table-info-name tf) 
             schema 
             (table-init-func (length schema) size))))
  (map (lambda (i) (gen-sym-table-from-info
                     (list-ref table-info-list i)
                     (list-ref table-size-list i)))
       (build-list (length table-size-list) values)))

; apply the assertion function to each table in the table list
(define (assert-sym-tables tables assert-func)
  (for-each (lambda (table) (assert-func table)) tables))

; apply assertions generated from mconstr to each table
(define (assert-sym-tables-mconstr tables mconstr)
  (let* ([mconstr-map (if (null? mconstr) (make-hash) (mconstr-to-hashmap mconstr))])
    (for-each (lambda (table)
                (let ([c (hash-ref mconstr-map (Table-name table) null)])
                  (if (null? c) (list) (assert-table-mconstr table c)))) tables)))

; given two query functions and the schema definition,
; the function will increase the table size one by one trying to solve the question
(define (solve-queries fq1 fq2 table-info-list messenger)
  (let* ([initial-size (init-table-size-list (list fq1 fq2) table-info-list)]
         [try-solve
           (lambda (fq1 fq2 table-info-list table-size-list)
             (let* ([tables (init-sym-tables table-info-list table-size-list)]
                    [q1 (fq1 tables)]
                    [q2 (fq2 tables)])
               (cosette-solve q1 q2 tables)))])
    (define (rec-wrapper table-size-list)
      (let ([sol (try-solve fq1 fq2 table-info-list table-size-list)])
        (cond [(eq? (car sol) "NEQ") (messenger sol)]
              [else (messenger  table-size-list)
                    (rec-wrapper (inc-table-size-list table-size-list))])))
    (rec-wrapper initial-size)))


; given two query functions and the schema definition,
; the function will increase the table size one by one trying to solve the question
; it differs from the one above as it utilize the symmetry breaking method
(define (solve-queries-symbreak fq1 fq2 table-info-list messenger)
  (let* ([initial-size (init-table-size-list (list fq1 fq2) table-info-list)]
         [try-solve
           (lambda (fq1 fq2 table-info-list table-size-list)
             (let* ([empty-tables (init-sym-tables table-info-list 
                                   (build-list (length table-info-list) (lambda (x) 0))
                                   gen-sym-schema)]
                    [mconstr (go-break-symmetry-bounded (fq1 empty-tables) (fq2 empty-tables))]
                    [tables (init-sym-tables table-info-list table-size-list)]
                    [q1 (fq1 tables)]
                    [q2 (fq2 tables)])
               (assert-sym-tables-mconstr tables mconstr)
               (cosette-solve q1 q2 tables)))])
    (define (rec-wrapper table-size-list)
      (let ([sol (time (try-solve fq1 fq2 table-info-list table-size-list))])
        (cond [(eq? (car sol) "NEQ") (messenger sol)]
              [else (messenger  table-size-list)
                    (rec-wrapper (inc-table-size-list table-size-list))])))
    (rec-wrapper initial-size)))

;; check which tables are used given a list of fq functions
(define (used-table-info fq-list table-info-list)
  ;; check which tables are involved in provided queries
  (letrec ([used-table-info-one
          (lambda (qtf) 
            (cond
              [(query-select? qtf) (used-table-info-one (query-select-from-query qtf))]
              [(query-select-distinct? qtf) 
               (used-table-info-one (query-select-distinct-from-query qtf))]
              [(query-join? qtf)
               (append (used-table-info-one (query-join-query1 qtf)) 
                       (used-table-info-one (query-join-query2 qtf)))]
              [(query-named? qtf) 
               (list (table-info-name (query-named-table-ref qtf)))]
              [(query-rename? qtf) (used-table-info-one (query-rename-query qtf))]
              [(query-rename-full? qtf) (used-table-info-one (query-rename-full-query qtf))]
              [(query-left-outer-join? qtf) 
               (append (used-table-info-one (query-left-outer-join-query1 qtf))
                       (used-table-info-one (query-left-outer-join-query2 qtf)))]
              [(query-union-all? qtf) 
               (append (used-table-info-one (query-union-all-query1 qtf))
                       (used-table-info-one (query-union-all-query2 qtf)))]
              [(query-aggr-general? qtf) (used-table-info-one (query-aggr-general-query qtf))]
              [else (error "[Error] not  query construct")]))])
    (list->set (foldl append (list)
                      (map (lambda (fq) (used-table-info-one (fq table-info-list))) fq-list)))))


