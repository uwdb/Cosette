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

; SELECT DISTINCT dept name FROM course
; WHERE credits=(SELECT MAX(credits) FROM course)

(define (q1 tables)
  (SELECT-DISTINCT (VALS "c.dept_name")
    FROM (JOIN (AS (SELECT (VALS (MAX "c.credits"))
                      FROM (NAMED (list-ref tables 0))
                     WHERE (TRUE)
                      GROUP-BY (list)
                      HAVING (TRUE))
                   ["a" (list "max_credits")])
               (NAMED (list-ref tables 0)))
   WHERE (BINOP "c.credits" = "a.max_credits")))

(define (q2 tables)
  (SELECT-DISTINCT (VALS "c.dept_name")
    FROM (JOIN (AS (SELECT (VALS (MAX "c.credits"))
                      FROM (NAMED (list-ref tables 0))
                     WHERE (TRUE)
                      GROUP-BY (list "c.dept_name")
                      HAVING (TRUE))
                   ["a" (list "max_credits")])
               (NAMED (list-ref tables 0)))
   WHERE (BINOP "c.credits" = "a.max_credits")))

;(define ros-instance (list q1 (list course department instructor teaches section takes student) (list) prop-table-empty)) 
(define ros-instance (list q1 q2 (list course department instructor teaches section takes student)))
