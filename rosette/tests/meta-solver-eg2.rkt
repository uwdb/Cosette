#lang rosette

(require "../meta-solver.rkt" "../sql.rkt" 
         "../syntax.rkt" "../denotation.rkt" 
         "../table.rkt" "../evaluator.rkt" "../util.rkt")

(current-bitwidth #f)

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
   (SELECT (VALS "t.id1" "t.cname" "t.id2")
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

(println (to-str-set (propogate q1 (list (init-constraint (length (extract-schema q1)) 1)) 1 999)))
