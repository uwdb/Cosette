#lang rosette

(require "../util.rkt" "../syntax.rkt" "../denotation.rkt" "../table.rkt"  "../evaluator.rkt" "../equal.rkt"  rosette/lib/synthax)

(current-bitwidth 5)

; ------- actual tables (only for test) -------

(define c-instructor
  (Table "i" (list "id" "name")
         (list
          (cons (list 1 1) 1)
          (cons (list 2 2) 1))))

(define c-teaches
  (Table "t" (list "cname" "id")
         (list
          (cons (list 2 3) 1))))

; ------------ symbolic tables ----------------
; we need at least two rows

(define s-instructor (Table "c" (list "id" "name") (gen-pos-sym-schema 2 1)))
(define s-teaches (Table "d" (list "cname" "id") (gen-pos-sym-schema 2 1)))

; ------------ count bug ----------------------
(define instructor s-instructor)
(define teaches s-teaches)

; SELECT * 
; FROM instructor JOIN teaches
; WHERE instructor.id == teaches.id

(define q1
   (SELECT (VALS "t.id1" "t.name" "t.cname" "t.id2")
    FROM  (AS (JOIN (NAMED instructor) (NAMED teaches))
	      ["t" (list "id1" "name" "cname" "id2")])
    WHERE (BINOP "t.id1" = "t.id2")))

; SELECT * 
; FROM instructor JOIN teaches
; WHERE instructor.id == teaches.id

(define q2
  (AS (LEFT-OUTER-JOIN (NAMED instructor) (NAMED teaches) 0 1)
      ["t1" (list "id1" "name" "cname" "id2")]))

(define q3
  (SELECT (VALS "t1.id1" "t1.name" "t1.cname" "t1.id2")
   FROM (AS (LEFT-OUTER-JOIN (NAMED teaches) (NAMED instructor) 1 0)
      	["t1" (list "cname" "id2" "id1" "name")])
   WHERE (filter-empty)))
; expect model
;(run q2)
;(run q4)
(time (verify (same q1 q2)))
(time (verify (same q1 q3)))


