#lang rosette

(current-bitwidth 10)

(require "../cosette.rkt" "../util.rkt" "../denotation.rkt" 
         "../sql.rkt" "../evaluator.rkt" "../syntax.rkt" "../symmetry.rkt") 

(provide ros-instance)

(define scores-info (table-info "Scores" (list "StudentID" "CourseID" "Points")))
(define students-info (table-info "Students" (list "StudentNr" "StudentName")))

; DECLARE @x as tinyint;
; SELECT Students.StudentName, SUM(Points)
; FROM Scores JOIN Students ON Scores.StudentID = Students.StudentNr
; WHERE Scores.Points > 2 AND Students.StudentName LIKE "John%"
; GROUP BY Students.StudentName
; HAVING SUM(Points) >= @x AND @x > 15

(define-symbolic* x integer?)

(define (q tables)
  (SELECT (VALS "Students.StudentName" (VAL-UNOP aggr-sum (val-column-ref "Scores.Points")))
   FROM   (JOIN (NAMED (list-ref tables 0)) (NAMED (list-ref tables 1)))
   WHERE  (AND (BINOP "Scores.StudentID" = "Students.StudentNr") (BINOP "Scores.Points" > 2))
   GROUP-BY (list "Students.StudentName")         
   HAVING (AND (BINOP (VAL-UNOP aggr-sum (val-column-ref "Scores.Points")) > x) 
               (BINOP x > 15))))

(define ros-instance (list q (list scores-info students-info) (list x) prop-table-empty))