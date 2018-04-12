#lang rosette 
 
(require "../cosette.rkt" "../util.rkt" "../denotation.rkt" 
         "../sql.rkt" "../evaluator.rkt" "../syntax.rkt" "../symmetry.rkt"
         "../table.rkt")
 
(provide ros-instance)

(current-bitwidth #f)

(define-symbolic div_ (~> integer? integer? integer?))

(define course (table-info "c" (list "course_id" "dept_name" "credits")))
(define department (table-info "d" (list "dept_name" "budget" "building")))
(define instructor (table-info "i" (list "salary" "dept_name")))
(define teaches (table-info "t" (list "course_id" "year" "semester")))

; SELECT t.semester, SUM(c.credits)
; FROM department d INNER JOIN teaches t
; ON (d.budget = t.year + 4)
; INNER JOIN course c
; ON (c.dept name = d.dept name)
; GROUP BY t.semester
; HAVING AVG(c.credits)>2 AND COUNT(d.building)=2

(define (q1 tables) 
  (SELECT (VALS "t.semester" (SUM "c.credits"))
   FROM (JOIN (JOIN (NAMED (list-ref tables 0))
                    (NAMED (list-ref tables 1)))
              (NAMED (list-ref tables 3)))
   WHERE (AND (BINOP "c.dept_name" = "d.dept_name")
              (BINOP "d.budget" = (VAL-BINOP "t.year" + 4)))
   GROUP-BY (list "c.dept_name")
   HAVING (AND (BINOP (VAL-BINOP (SUM "c.credits") div_ (COUNT "c.credits")) > 100000)
               (BINOP (COUNT "d.building") = 2))))

(define (q2 tables) 
  (SELECT (VALS "t.semester" (SUM "c.credits"))
   FROM (JOIN (JOIN (NAMED (list-ref tables 0))
                    (NAMED (list-ref tables 1)))
              (NAMED (list-ref tables 3)))
   WHERE (AND (BINOP "c.dept_name" = "d.dept_name")
              (BINOP "d.budget" >= (VAL-BINOP "t.year" + 4)))
   GROUP-BY (list "c.dept_name")
   HAVING (AND (BINOP (VAL-BINOP (SUM "c.credits") div_ (COUNT "c.credits")) > 100000)
               (BINOP (COUNT "d.building") = 2))))

;(define ros-instance (list q1 (list course department instructor teaches) (list) prop-table-empty)) 

(define ros-instance (list q1 q2 (list course department instructor teaches)))
