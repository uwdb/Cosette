#lang rosette

(require "../cosette.rkt" "../util.rkt" "../table.rkt"
         "../sql.rkt" "../evaluator.rkt" "../equal.rkt")

(define (fq1 tables)
  (SELECT (VALS "t1.id")
   FROM   (NAMED (list-ref tables 0))
   WHERE  (BINOP "t1.id" = 1)))
(define (fq2 tables) (NAMED (list-ref tables 0)))
(define (fq3 tables) (NAMED (list-ref tables 0)))

(define t1-info (table-info "t1" (list "id")))
(define t2-info (table-info "t2" (list "id")))

(define tabs (list (gen-sym-table-from-info t1-info 3)))

;; (car (let ([q1 (fq1 tabs)]
;;       [q2 (fq2 tabs)])
;;   (cosette-solve q1 q2 tabs)))

; this one returns neq pretty quickly
(solve-queries fq1 fq2 (list t1-info) println)
; this one will never return unequal, but keep increasing table size
;(solve-queries fq3 fq2 (list t1-info t2-info) println)

;(define (cosette-solve-new fq1 fq2 table-infos)
;  )

;(cosette-sol->json (cosette-solve q1 q2 (list t1 t2)))
;(map (lambda (t) (table-to-json-obj t)) (cosette-verify q1 q2 (list t1 t2)))
;(time (verify (same q1 q2)))
;(time (verify (neq q1 q2)))
