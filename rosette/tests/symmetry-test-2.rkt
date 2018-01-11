#lang rosette

(require "../symmetry.rkt" "../sql.rkt" 
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

(define q32
   (SELECT-DISTINCT (VALS "t.id1" "t.name" "t.cname" "t.id2")
    FROM  (AS (JOIN (NAMED instructor) (NAMED teaches))
        ["t" (list "id1" "name" "cname" "id2")])
    WHERE (BINOP "t.id1" < "t.id2")))

(define q4
   (SELECT (VALS "t.id1" "t.name" "t.cname" "t.id2")
    FROM  (AS (JOIN (NAMED instructor) (NAMED teaches))
        ["t" (list "id1" "name" "cname" "id2")])
    WHERE (BINOP "t.id1" >= "t.id2")))

(define c2 (small-step-sum-eq (init-constraint q1) 0))
(define c3 (big-step (init-constraint q3) 10))
(define xxx (init-constraint q32))
(define c32 (big-step xxx 10))


(displayln (to-str c3))
(displayln (to-str c32))
;"SumEQ((r[0] = r[3]) ∧ ((r[3] = $2) ∧ (r[2] = $1) ∧ (r[0] = $0)))"
;"∀{ (rc8[0] = rd9[1]) ∧ ((rd9[1] = @2) ∧ (rd9[0] = @1) ∧ (rc8[0] = @0)) }  "


