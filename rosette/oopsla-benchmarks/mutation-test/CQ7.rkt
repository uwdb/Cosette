#lang rosette 
 
(require "../cosette.rkt" "../util.rkt" "../denotation.rkt" 
         "../sql.rkt" "../evaluator.rkt" "../syntax.rkt" "../symmetry.rkt"
         "../table.rkt")
 
(provide ros-instance)

(current-bitwidth #f)

(define-symbolic div_ (~> integer? integer? integer?))

(define instructor (table-info "i" (list "id" "name" "dept_name")))
(define teaches (table-info "t" (list "id" "course_id" "year" "semester")))

; SELECT DISTINCT instructor.id, name, course id
; FROM instructor LEFT OUTER JOIN TEACHES
; ON instructor.id = teaches.id

(define (q1 tables)
  (SELECT-DISTINCT (VALS "i.id" "i.name" "t.course_id")
   FROM (LEFT-OUTER-JOIN (NAMED (list-ref tables 0))
                         (NAMED (list-ref tables 1))
                         (BINOP "i.id" > "t.id"))
   WHERE (TRUE)))

(define (q2 tables)
  (SELECT-DISTINCT (VALS "i.id" "i.name" "t.course_id")
   FROM (JOIN (NAMED (list-ref tables 0))
              (NAMED (list-ref tables 1)))
   WHERE (BINOP "i.id" = "t.id")))


(define ros-instance (list q1 q2 (list instructor teaches)))