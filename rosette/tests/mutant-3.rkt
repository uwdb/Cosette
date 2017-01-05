#lang rosette

(require "test-util.rkt" "../table.rkt" "../sql.rkt" "../evaluator.rkt" "../equal.rkt"  rosette/lib/synthax)

(define (same q1 q2)
    (assert (bag-equal (get-content (run q1)) (get-content (run q2)))))

(current-bitwidth 5)

; TODO: move to a separate file
; count aggregation function
(define (aggr-count l)
  (foldl + 0 (map cdr (get-content l))))

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

(define q2
   (SELECT (VALS "t.id1" "t.name" "t.cname" "t.id2")
    FROM  (AS (JOIN (NAMED instructor) (NAMED teaches))
	      ["t" (list "id1" "name" "cname" "id2")])
    WHERE (BINOP "t.id1" <= "t.id2")))

(define q3
   (SELECT (VALS "t.id1" "t.name" "t.cname" "t.id2")
    FROM  (AS (JOIN (NAMED instructor) (NAMED teaches))
	      ["t" (list "id1" "name" "cname" "id2")])
    WHERE (BINOP "t.id1" < "t.id2")))

(define q4
   (SELECT (VALS "t.id1" "t.name" "t.cname" "t.id2")
    FROM  (AS (JOIN (NAMED instructor) (NAMED teaches))
	      ["t" (list "id1" "name" "cname" "id2")])
    WHERE (BINOP "t.id1" >= "t.id2")))

; expect model
;(run q2)
;(run q4)
(time (verify (same q1 q2)))
(time (verify (same q1 q3)))
(time (verify (same q1 q4)))


