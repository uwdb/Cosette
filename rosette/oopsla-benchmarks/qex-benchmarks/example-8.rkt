#lang rosette

(current-bitwidth 10)

(require "../cosette.rkt" "../util.rkt" "../denotation.rkt" 
         "../sql.rkt" "../evaluator.rkt" "../syntax.rkt" "../symmetry.rkt") 

(provide ros-instance)

(define scores-info (table-info "Scores" (list "StudentID" "CourseID" "Points")))
(define students-info (table-info "Students" (list "StudentNr" "StudentName")))

; SELECT Students.StudentName, Scores.Points
; FROM Students JOIN Scores ON Scores.StudentID = Students.StudentNr
; WHERE Scores.CourseID = 10 AND Scores.Points > 0

(define (q tables)
  (SELECT (VALS "Students.StudentName" "Scores.Points")
   FROM   (JOIN (NAMED (list-ref tables 0)) (NAMED (list-ref tables 1)))
   WHERE  (AND (AND (BINOP "Scores.StudentID" = "Students.StudentNr") 
                    (BINOP "Scores.Points" > 0))
               (BINOP "Scores.CourseID" = 10))))

(define ros-instance (list q (list scores-info students-info) (list) prop-table-empty))