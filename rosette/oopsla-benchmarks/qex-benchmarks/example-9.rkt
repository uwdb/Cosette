#lang rosette

(current-bitwidth 10)

(require "../cosette.rkt" "../util.rkt" "../denotation.rkt" 
         "../sql.rkt" "../evaluator.rkt" "../syntax.rkt" "../symmetry.rkt") 

(provide ros-instance)

(define scores-info (table-info "Scores" (list "StudentID" "CourseID" "Points")))
(define students-info (table-info "Students" (list "StudentNr" "StudentName")))
(define courses-info (table-info "Courses" (list "CourseNr" "CourseName")))

; SELECT Students.StudentName, Courses.CourseName, Scores.Points
; FROM Scores JOIN Students ON Scores.StudentID = Students.StudentNr
; JOIN Courses ON Courses.CourseNr = Scores.CourseID
; WHERE Scores.Points > 2 AND Students.StudentName LIKE "%bob%"
; AND Courses.CourseName LIKE "AI%"

(define (q tables)
  (SELECT (VALS "Students.StudentName" "Courses.CourseName" "Scores.Points")
   FROM   (JOIN (JOIN (NAMED (list-ref tables 0)) (NAMED (list-ref tables 1))) (NAMED (list-ref tables 2)))
   WHERE  (AND (AND (BINOP "Scores.StudentID" = "Students.StudentNr") 
                    (BINOP "Scores.CourseID" = "Courses.CourseNr"))
               (BINOP "Scores.Points" > 2))))

(define ros-instance (list q (list scores-info students-info courses-info) (list) prop-table-empty))