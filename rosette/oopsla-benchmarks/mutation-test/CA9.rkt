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

; SELECT SUM(T) as su FROM
; (SELECT year as T
; FROM teaches NATURAL JOIN instructor
; GROUP BY year, course id HAVING COUNT(id)>4)
; as temp GROUP BY T

(define (q1 tables)
  (SELECT (VALS (SUM "a.year"))
   FROM (AS (SELECT (VALS "t.year")
              FROM (JOIN (NAMED (list-ref tables 2))
                         (NAMED (list-ref tables 3)))
              WHERE (BINOP "t.ID" = "i.ID")
              GROUP-BY (list "t.year" "t.course_id")
              HAVING (BINOP (COUNT "i.ID") > 4))
            ["a" (list "year")])
   WHERE (TRUE)
   GROUP-BY (list "a.year")
   HAVING (TRUE)))

(define (q2 tables)
  (SELECT (VALS (SUM "a.year"))
   FROM (AS (SELECT (VALS "t.year")
              FROM (JOIN (NAMED (list-ref tables 2))
                         (NAMED (list-ref tables 3)))
              WHERE (BINOP "t.ID" = "i.ID")
              GROUP-BY (list "t.year")
              HAVING (BINOP (COUNT "i.ID") > 4))
            ["a" (list "year")])
   WHERE (TRUE)
   GROUP-BY (list "a.year")
   HAVING (TRUE)))

;(define ros-instance (list q1 (list course department instructor teaches section takes student) (list) prop-table-empty)) 
(define ros-instance (list q1 q2 (list course department instructor teaches section takes student)))
