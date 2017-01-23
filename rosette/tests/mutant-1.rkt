#lang rosette

(require "../util.rkt" "../syntax.rkt" "../denotation.rkt" "../table.rkt"  "../evaluator.rkt" "../equal.rkt"  rosette/lib/synthax)

(current-bitwidth 32)

; ------- actual tables (only for test) -------

(define c-course
  (Table "c" (list "id" "dept")
         (list
          (cons (list 0 1) 8)
          (cons (list 2 2) 15))))

(define c-department
  (Table "d" (list "dept" "budget")
         (list
          (cons (list 2 70001) 2))))

; ------------ symbolic tables ----------------
; we need at least two rows

(define s-course (Table "c" (list "id" "dept") (gen-sym-schema 2 1)))

(define s-department (Table "d" (list "dept" "budget") (gen-sym-schema 2 1)))

; ------------ count bug ----------------------
(define course s-course)
(define department s-department)

;SELECT course.id, department.dept name FROM course LEFT
;OUTER JOIN (SELECT * from department
;		   WHERE department.budget > 70000) d USING (dept name);

(define q1
  (AS
   (SELECT (VALS "d.dept" "d.budget")
    FROM  (NAMED department)
    WHERE (BINOP "d.budget" > 70000))
   ["t1" (list "dept" "budget")]))

(define q2
  (LEFT-OUTER-JOIN (NAMED course) q1 1 0))

;SELECT course.id, department.dept name FROM course LEFT
;OUTER JOIN department USING (dept name)
;WHERE department.budget > 70000;

(define q3
  (AS (LEFT-OUTER-JOIN (NAMED course) (NAMED department) 1 0)
      ["t1" (list "id" "dept1" "dept2" "budget")]))

(define q4
  (SELECT (VALS "t1.dept2" "t1.budget")
    FROM  q3
    WHERE (BINOP "t1.budget" > 70000)))

; expect model
;(run q2)
;(run q4)
(time (verify (same q2 q4)))
