#lang rosette 
 
(require "../cosette.rkt" "../util.rkt" "../denotation.rkt" 
         "../sql.rkt" "../evaluator.rkt" "../syntax.rkt" "../symmetry.rkt"
         "../table.rkt") 
 
(provide ros-instance)
 
(current-bitwidth #f)
 
(define course (table-info "c" (list "course_id" "title" "dept_name" "credits")))
(define department (table-info "d" (list "dept_name" "building" "budget")))
(define instructor (table-info "i" (list "ID" "name" "dept_name" "salary")))
(define teaches (table-info "t" (list "ID" "course_id" "sec_id" "year")))
(define section (table-info "s" (list "course_id" "sec_id" "year" "building" "room_number" "time_slot_id")))
(define takes (table-info "takes" (list "ID" "course_id" "sec_id" "year" "grade")))
(define student (table-info "student" (list "ID" "name" "dept_name" "tot_cred")))

; SELECT c.dept_name, SUM(c.credits)
; FROM course c INNER JOIN department d
; ON (c.dept name = d.dept name)
; GROUP BY c.dept name
; HAVING SUM(c.credits)>10 AND COUNT(c.credits)>1
(define (q1 tables) 
  (SELECT (VALS "c.dept_name" (SUM "c.credits"))
   FROM (JOIN (NAMED (list-ref tables 0))
              (NAMED (list-ref tables 1)))
   WHERE (BINOP "c.dept_name" = "d.dept_name")
   GROUP-BY (list "c.dept_name")
   HAVING (AND (BINOP (SUM "c.credits") > 10)
               (BINOP (COUNT-DISTINCT "c.credits") > 3))))

(define (q2 tables) 
  (SELECT (VALS "c.dept_name" (SUM "c.credits"))
   FROM (JOIN (NAMED (list-ref tables 0))
              (NAMED (list-ref tables 1)))
   WHERE (BINOP "c.dept_name" = "d.dept_name")
   GROUP-BY (list "c.dept_name")
   HAVING (AND (BINOP (SUM "c.credits") > 10)
               (BINOP (COUNT-DISTINCT "c.credits") > 5))))

;(define ros-instance (list q1 (list course department) (list) prop-table-empty)) 
(define ros-instance (list q1 q2 (list course department))) 
