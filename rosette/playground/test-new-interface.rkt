#lang rosette

(require "../cosette.rkt" "../util.rkt" "../table.rkt" "../denotation.rkt"
         "../sql.rkt" "../evaluator.rkt" "../equal.rkt" "../syntax.rkt")

; note: the new interface requires rewrite all the queries to the following form

(define (fq1 tables)
  (SELECT (VALS "t1.id")
   FROM   (NAMED (list-ref tables 0))
   WHERE  (BINOP "t1.id" = 1)))

(define (fq2 tables) (NAMED (list-ref tables 0)))
(define (fq3 tables) (NAMED (list-ref tables 0)))

; a struct stores table name and schema
(struct table-info (name schema)
  #:transparent
  #:guard (lambda (name schema type-name)
            (cond
              [(not (string? name)) (error type-name "bad name:~e" name)]
              [(not (list? schema)) (error type-name "bad schema:~e" schema)]
              [else (values name schema)])))

; generate a symbolic table according to table-info and size
(define (gen-table tf size)
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
(define (solve-queries fq1 fq2 table-info-list)
  (let* ([init-table-size-list
         (init-table-size-list (length table-info-list))]
        [try-solve
         (lambda (fq1 fq2 table-info-list table-size-list)
           (let* ([tables (map (lambda (i) (gen-table (list-ref table-info-list i)
                                                      (list-ref table-size-list i)))
                               (build-list (length table-info-list) values))]
                  [q1 (fq1 tables)]
                  [q2 (fq2 tables)])
             (cosette-solve q1 q2 tables)))])
    (define (rec-wrapper table-size-list)
           (let ([sol (try-solve fq1 fq2 table-info-list table-size-list)])
              (cond [(eq? (car sol) "neq") sol]
            [else (println table-size-list)
                  (rec-wrapper (inc-table-size-list table-size-list))])))
    (rec-wrapper init-table-size-list)))

;;;;;;;;;;; Code below are served for testing purpose

(define t1-info (table-info "t1" (list "id")))
(define t2-info (table-info "t2" (list "id")))

(define tabs (list (gen-table t1-info 3)))

(car (let ([q1 (fq1 tabs)]
      [q2 (fq2 tabs)])
  (cosette-solve q1 q2 tabs)))

; this one returns neq pretty quickly
(solve-queries fq1 fq2 (list t1-info))
; this one will never return unequal, but keep increasing table size
(solve-queries fq3 fq2 (list t1-info t2-info))

;(define (cosette-solve-new fq1 fq2 table-infos)
;  )

;(cosette-sol->json (cosette-solve q1 q2 (list t1 t2)))
;(map (lambda (t) (table-to-json-obj t)) (cosette-verify q1 q2 (list t1 t2)))
;(time (verify (same q1 q2)))
;(time (verify (neq q1 q2)))
