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

; SELECT id
; FROM course NATURAL JOIN department
; NATURAL JOIN student NATURAL JOIN takes
; NATURAL JOIN section
; GROUP BY id,dept name HAVING COUNT(dept name) > 1

(define (q1 tables) 
  (SELECT (VALS "student.ID")
   FROM (JOIN (JOIN (JOIN (NAMED (list-ref tables 0))
                          (NAMED (list-ref tables 6)))
                    (NAMED (list-ref tables 5)))
              (NAMED (list-ref tables 4)))
   WHERE (AND (AND (AND (AND (BINOP "c.dept_name" = "student.dept_name")
                   		(BINOP "c.course_id" = "takes.course_id"))
                   (BINOP "student.ID" = "takes.ID"))
              (BINOP "s.sec_id" = "takes.sec_id"))
              (BINOP "s.course_id" = "c.course_id"))
   GROUP-BY (list "student.ID" "student.dept_name")
   HAVING (BINOP (COUNT "c.course_id") > 1)))

(define (q2 tables)
  (SELECT (VALS "student.ID")
   FROM (JOIN (JOIN (JOIN (NAMED (list-ref tables 0))
                          (NAMED (list-ref tables 6)))
                    (NAMED (list-ref tables 5)))
              (NAMED (list-ref tables 4)))
   WHERE (AND (AND (AND (AND (BINOP "c.dept_name" = "student.dept_name")
                   		(BINOP "c.course_id" = "takes.course_id"))
                   (BINOP "student.ID" >= "takes.ID"))
              (BINOP "s.sec_id" = "takes.sec_id"))
              (BINOP "s.course_id" = "c.course_id"))
   GROUP-BY (list "student.ID" "student.dept_name")
   HAVING (BINOP (COUNT "c.course_id") >= 2)))

;(define ros-instance (list q1 (list course department instructor teaches section takes student) (list) prop-table-empty)) 
(define ros-instance (list q1 q2 (list course department instructor teaches section takes student))) 
