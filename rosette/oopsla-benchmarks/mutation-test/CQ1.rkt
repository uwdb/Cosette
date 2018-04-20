#lang rosette 
 
(require "../cosette.rkt" "../util.rkt" "../denotation.rkt" 
         "../sql.rkt" "../evaluator.rkt" "../syntax.rkt" "../symmetry.rkt"
         "../table.rkt")
 
(provide ros-instance)

(current-bitwidth #f)

(define-symbolic div_ (~> integer? integer? integer?))

(define course (table-info "c" (list "course_id" "dept_name" "credits" "title")))
(define department (table-info "d" (list "dept_name" "budget" "building")))
(define instructor (table-info "i" (list "salary" "dept_name")))
(define teaches (table-info "t" (list "course_id" "year" "semester")))

; SELECT course id, title FROM course

(define (q1 tables)
  (SELECT (VALS "c.course_id" "c.title")
   FROM (NAMED (list-ref tables 0))
   WHERE (TRUE)))

(define (q2 tables)
  (SELECT (VALS "c.course_id" "c.title")
   FROM (NAMED (list-ref tables 0))
   WHERE (BINOP "c.credits" > 3)))

(define ros-instance (list q1 q2 (list course department instructor teaches))) 

;(define ros-instance (list q1 (list course department instructor))) 