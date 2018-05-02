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

; SELECT DISTINCT course id, title, id
; FROM course NATURAL JOIN teaches
; WHERE teaches.semester = ‘Spring’
; AND teaches.year = ‘2010’

(define (q1 tables)
  (SELECT-DISTINCT (VALS "c.course_id" "c.title" "t.ID")
   FROM (JOIN (NAMED (list-ref tables 0))
              (NAMED (list-ref tables 3)))
   WHERE (AND (BINOP "c.course_id" = "t.course_id")
              (BINOP "t.year" = 2010))))

(define (q2 tables)
  (SELECT-DISTINCT (VALS "c.course_id" "c.title" "t.ID")
   FROM (JOIN (NAMED (list-ref tables 0))
              (NAMED (list-ref tables 3)))
   WHERE (AND (BINOP "c.course_id" >= "t.course_id")
              (BINOP "t.year" = 2010))))

(define ros-instance (list q1 q2 (list course department instructor teaches section takes student)))