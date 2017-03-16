#lang rosette

(require "../cosette.rkt" "../util.rkt" "../table.rkt" "../denotation.rkt"
         "../sql.rkt" "../evaluator.rkt" "../equal.rkt" "../syntax.rkt")

; note: the new interface requires rewrite all the queries to the following form

(define (fq1 tables)
  (SELECT (VALS "t1.id")
   FROM   (NAMED (list-ref tables 0))
   WHERE  (BINOP "t1.id" = 1)))

(define (fq2 tables) (NAMED (list-ref tables 0)))

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

(define t1-info (table-info "t1" (list "id")))

(define tabs (list (gen-table t1-info 3)))

(let ([q1 (fq1 tabs)]
      [q2 (fq2 tabs)])
  (cosette-solve q1 q2 tabs))

;(define (cosette-solve-new fq1 fq2 table-infos)
;  )

;(cosette-sol->json (cosette-solve q1 q2 (list t1 t2)))
;(map (lambda (t) (table-to-json-obj t)) (cosette-verify q1 q2 (list t1 t2)))
;(time (verify (same q1 q2)))
;(time (verify (neq q1 q2)))
