; The rosette interface for cosette

#lang rosette

(require "util.rkt" "table.rkt" "equal.rkt" "syntax.rkt" "denotation.rkt")
(require racket/pretty)
(require json)

(provide cosette-sol->json 
         cosette-solve
         table-info
         solve-queries
         gen-sym-table-from-info)

; format cosette solution into a json string
; {
;    "status": ... // "eq" or "neq"
;    "counter-example": [ 
;       {
;        "table-name": ..., // a string representing table name
;        "table-content": ...// a list of lists representing the table content, first list is schema
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

(define (cosette-solve q1 q2 input-tables)
  (let ([solution (verify (same q1 q2))])
    (cond 
      [(sat? solution) (cons "neq" (evaluate input-tables solution))]
      [else (cons "eq"  (list))]))) 

(define (table->jsexpr t) 
  (hasheq 'table-name (get-table-name t) 
          'table-content (list (get-schema t) 
                               (map (lambda (r)
                                      (list (map sv->string (car r))
                                            (sv->string (cdr r)))) 
                                    (get-content t)))))

(define (sv->string v)
  (if (term? v) (term->string) v))

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

; generate a symbolic table according to table-info and size
(define (gen-sym-table-from-info tf size)
  (let ([schema (table-info-schema tf)])
    (Table (table-info-name tf) schema (gen-sym-schema (length schema) size)))) 

; initialize the table size list
(define (init-table-size-list table-num)
  (make-list table-num 1))

; given a list of table sizes, increase the size of them one at a time (zig-zag style)
(define (inc-table-size-list size-list)
  (match size-list
         [(list x) (list (+ x 1))]
         [(cons x l)
          (cond [(< x (car l)) (append (list (+ x 1)) l)]
                [else (append (list x) (inc-table-size-list l))])]))

; given two query functions and the schema definition,
; the function will increase the table size one by one trying to solve the question
(define (solve-queries fq1 fq2 table-info-list messenger)
  (let* ([init-table-size-list
           (init-table-size-list (length table-info-list))]
         [try-solve
           (lambda (fq1 fq2 table-info-list table-size-list)
             (let* ([tables (map (lambda (i) (gen-sym-table-from-info (list-ref table-info-list i)
                                                        (list-ref table-size-list i)))
                                 (build-list (length table-info-list) values))]
                    [q1 (fq1 tables)]
                    [q2 (fq2 tables)])
               (cosette-solve q1 q2 tables)))])
    (define (rec-wrapper table-size-list)
      (let ([sol (try-solve fq1 fq2 table-info-list table-size-list)])
        (cond [(eq? (car sol) "neq") (messenger sol)]
              [else (messenger  table-size-list)
                    (rec-wrapper (inc-table-size-list table-size-list))])))
    (rec-wrapper init-table-size-list)))
