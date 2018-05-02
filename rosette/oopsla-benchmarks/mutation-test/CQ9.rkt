#lang rosette 
 
(require "../cosette.rkt" "../util.rkt" "../denotation.rkt" 
         "../sql.rkt" "../evaluator.rkt" "../syntax.rkt" "../symmetry.rkt"
         "../table.rkt")
 
(provide ros-instance)

(current-bitwidth #f)

(define-symbolic div_ (~> integer? integer? integer?))

(define course (table-info "c" (list "course_id" "title" "dept_name" "credits")))
(define department (table-info "d" (list "dept_name" "building" "budget")))
(define instructor (table-info "i" (list "ID" "name" "dept_name" "salary")))
(define teaches (table-info "t" (list "ID" "course_id" "sec_id" "year")))
(define section (table-info "s" (list "course_id" "sec_id" "year" "building" "room_number" "time_slot_id")))
(define takes (table-info "takes" (list "ID" "course_id" "sec_id" "year" "grade")))
(define student (table-info "student" (list "ID" "name" "dept_name" "tot_cred")))

;  WITH s as
; (SELECT id, time slot id, year, semester
; FROM takes NATURAL JOIN section
; GROUP BY id, time slot id, year, semester
; HAVING COUNT(time slot id)>1)
; 
; SELECT DISTINCT id,name
; FROM s NATURAL JOIN student

(define (q1 tables)
  (SELECT-DISTINCT (VALS "a.ID" "student.name")
    FROM (JOIN (AS (SELECT (VALS "takes.ID" "s.time_slot_id" "s.year")
                      FROM (JOIN (NAMED (list-ref tables 4))
                                 (NAMED (list-ref tables 5)))
                      WHERE (AND (BINOP "takes.course_id" = "s.course_id")
                                 (BINOP "takes.sec_id" = "s.sec_id"))
                      GROUP-BY (list "takes.ID" "s.time_slot_id" "s.year")
                      HAVING (BINOP (COUNT-DISTINCT "s.time_slot_id") > 4))
                   ["a" (list "ID" "time_slot_id" "year")])
               (NAMED (list-ref tables 6)))
   WHERE (BINOP "a.ID" = "student.ID")))

(define (q2 tables)
  (SELECT-DISTINCT (VALS "a.ID" "student.name")
    FROM (JOIN (AS (SELECT (VALS "takes.ID" "s.time_slot_id" "s.year")
                      FROM (JOIN (NAMED (list-ref tables 4))
                                 (NAMED (list-ref tables 5)))
                      WHERE (AND (BINOP "takes.course_id" = "s.course_id")
                                 (BINOP "takes.sec_id" = "s.sec_id"))
                      GROUP-BY (list "takes.ID" "s.time_slot_id" "s.year")
                      HAVING (BINOP (COUNT-DISTINCT "s.time_slot_id") > 5))
                   ["a" (list "ID" "time_slot_id" "year")])
               (NAMED (list-ref tables 6)))
   WHERE (BINOP "a.ID" = "student.ID")))

(define ros-instance (list q1 q2 (list course department instructor teaches section takes student)))
;(define ros-instance (list q1 (list course department instructor))) 