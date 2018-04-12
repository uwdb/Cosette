#lang rosette 
 
(require "../cosette.rkt" "../util.rkt" "../denotation.rkt" 
         "../sql.rkt" "../evaluator.rkt" "../syntax.rkt" "../symmetry.rkt"
         "../table.rkt")
 
(provide ros-instance)

(current-bitwidth #f)

(define-symbolic div_ (~> integer? integer? integer?))

(define course (table-info "c" (list "course_id" "dept_name" "course")))
(define department (table-info "d" (list "dept_name" "budget")))
(define instructor (table-info "i" (list "salary" "dept_name")))
(define teaches (table-info "t" (list "course_id" "instructor")))

; SELECT c.dept name, SUM(d.budget)
; FROM course c INNER JOIN department d
; ON (c.dept name = d.dept name)
; INNER JOIN teaches t
; ON (c.course id = t.course id)
; GROUP BY c.dept name
; HAVING SUM(d.budget)>100000 AND COUNT(d.budget)>1

(define (q1 tables) 
  (SELECT (VALS "c.dept_name" (SUM "d.budget"))
   FROM (JOIN (JOIN (NAMED (list-ref tables 0))
                    (NAMED (list-ref tables 1)))
              (NAMED (list-ref tables 3)))
   WHERE (AND (BINOP "c.dept_name" = "d.dept_name")
              (BINOP "c.course_id" = "t.course_id"))
   GROUP-BY (list "c.dept_name")
   HAVING (AND (BINOP (SUM "d.budget") > 100000)
               (BINOP (COUNT "d.budget") > 1))))

(define (q2 tables) 
  (SELECT (VALS "c.dept_name" (SUM "d.budget"))
   FROM (JOIN (JOIN (NAMED (list-ref tables 0))
                    (NAMED (list-ref tables 1)))
              (NAMED (list-ref tables 3)))
   WHERE (AND (BINOP "c.dept_name" = "d.dept_name")
              (BINOP "c.course_id" = "t.course_id"))
   GROUP-BY (list "c.dept_name")
   HAVING (AND (BINOP (SUM "d.budget") > 100000)
               (BINOP (COUNT-DISTINCT "d.budget") > 1))))

;(define ros-instance (list q1 (list course department instructor teaches) (list) prop-table-empty)) 

(define ros-instance (list q1 q2 (list course department instructor teaches))) 
