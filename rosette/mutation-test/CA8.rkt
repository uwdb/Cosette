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

; SELECT distinct dept name
; FROM course WHERE credits =
; (SELECT MAX(credits)
; FROM course NATURAL JOIN department
; WHERE title=‘CS’
; GROUP BY dept name HAVING COUNT(course id)>2)

(define (q1 tables)
  (SELECT (VALS "student.ID" "student.name")
   FROM (JOIN (NAMED (list-ref tables 6))
              (AS (SELECT (VALS "takes.ID" "s.time_slot_id" "s.year")
                   FROM (JOIN (NAMED (list-ref tables 5))
                              (NAMED (list-ref tables 4)))
                   WHERE (AND (BINOP "takes.course_id" = "s.course_id") 
                              (BINOP "takes.sec_id" = "s.sec_id"))
                   GROUP-BY (list "takes.ID" "s.time_slot_id" "s.year")
                   HAVING (BINOP (COUNT "s.time_slot_id") > 1))
                  ["a" (list "ID" "time_slot_id" "year")]))
   WHERE (BINOP "student.ID" = "a.ID")
   GROUP-BY (list "student.ID" "student.name")
   HAVING (BINOP (COUNT-DISTINCT "student.ID") > 2)))

(define (q2 tables)
  (SELECT (VALS "student.ID" "student.name")
   FROM (JOIN (NAMED (list-ref tables 6))
              (AS (SELECT (VALS "takes.ID" "s.time_slot_id" "s.year")
                   FROM (JOIN (NAMED (list-ref tables 5))
                              (NAMED (list-ref tables 4)))
                   WHERE (AND (BINOP "takes.course_id" = "s.course_id") 
                              (BINOP "takes.sec_id" = "s.sec_id"))
                   GROUP-BY (list "takes.ID" "s.time_slot_id" "s.year")
                   HAVING (BINOP (SUM "s.time_slot_id") > 1))
                  ["a" (list "ID" "time_slot_id" "year")]))
   WHERE (BINOP "student.ID" = "a.ID")
   GROUP-BY (list "student.ID" "student.name")
   HAVING (BINOP (COUNT-DISTINCT "student.ID") > 2)))

;(define ros-instance (list q1 (list course department instructor teaches section takes student) (list) prop-table-empty)) 
(define ros-instance (list q1 q2 (list course department instructor teaches section takes student)))
