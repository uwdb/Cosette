#lang rosette 
 
(require "../cosette.rkt" "../util.rkt" "../denotation.rkt" 
         "../sql.rkt" "../evaluator.rkt" "../syntax.rkt" "../symmetry.rkt"
         "../table.rkt")
 
(provide ros-instance)

(current-bitwidth #f)

(define-symbolic div_ (~> integer? integer? integer?))

(define course (table-info "c" (list "course_id" "dept_name" "course_tuple_type" "course")))
(define department (table-info "d" (list "dept_name" "budget")))
(define instructor (table-info "i" (list "salary" "dept_name")))

; SELECT c.dept name, SUM(i.salary)
; FROM course c INNER JOIN department d
; ON (c.dept name = d.dept name)
; INNER JOIN instructor i
; ON (d.dept name = i.dept name)
; GROUP BY c.dept name
; HAVING SUM(i.salary)>100000
; AND MAX(i.salary)<75000

(define (q1 tables) 
  (SELECT (VALS "c.dept_name" (SUM "i.salary"))
   FROM (JOIN (JOIN (NAMED (list-ref tables 0))
                    (NAMED (list-ref tables 1)))
              (NAMED (list-ref tables 2)))
   WHERE (AND (BINOP "c.dept_name" = "d.dept_name")
              (BINOP "d.dept_name" = "i.dept_name"))
   GROUP-BY (list "c.dept_name")
   HAVING (AND (BINOP (SUM "i.salary") > 100)
               (BINOP (MAX "i.salary") < 75))))

(define (q2 tables) 
  (SELECT (VALS "c.dept_name" (SUM "i.salary"))
   FROM (JOIN (JOIN (NAMED (list-ref tables 0))
                    (NAMED (list-ref tables 1)))
              (NAMED (list-ref tables 2)))
   WHERE (AND (BINOP "c.dept_name" = "d.dept_name")
              (BINOP "d.dept_name" = "i.dept_name"))
   GROUP-BY (list "c.dept_name")
   HAVING (AND (BINOP (SUM "i.salary") >= 100)
               (BINOP (MAX "i.salary") < 75))))

;(define ros-instance (list q1 (list course department instructor) (list) prop-table-empty)) 
(define ros-instance (list q1 q2 (list course department instructor))) 
