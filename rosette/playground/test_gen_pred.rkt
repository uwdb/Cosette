#lang rosette

(require "../cosette.rkt" "../util.rkt" "../table.rkt" 
         "../sql.rkt" "../evaluator.rkt" "../equal.rkt")

(define t1 (Table "t1" (list "id") (gen-sym-schema 1 3)))
(define t2 (Table "t2" (list "id") (list)))

(define-symbolic p1 (~> integer? integer? boolean?)) 

;(define t2 (Table "t1" (list "id") (list (cons (list 0) 0))))

; SELECT * AS u FROM users WHERE id = 1

(define q1
  (SELECT (VALS "t1.id")
   FROM   (NAMED t1)
   WHERE  (UF p1 "t1.id" "t1.id"))) 

(define q2 (NAMED t2))

(time (verify (same q1 q2)))
