#lang rosette

(current-bitwidth 10)

(require "../cosette.rkt" "../util.rkt" "../denotation.rkt" 
         "../sql.rkt" "../evaluator.rkt" "../syntax.rkt" "../symmetry.rkt") 

(provide ros-instance)

(define scores-info (table-info "Scores" (list "StudentID" "CourseID" "Points")))
(define students-info (table-info "Students" (list "StudentNr" "StudentName")))

; SELECT Scores.StudentID, MAX(Scores.Points)
; FROM Scores
; GROUP BY Scores.StudentID
; HAVING MAX(Scores.Points) = (SELECT MAX(Scores.Points) FROM Scores)

(define (q tables)
  (SELECT (VALS "t1.StudentID" "t1.Points")
   FROM (JOIN 
          (AS (SELECT (VALS "Scores.StudentID" 
                            (VAL-UNOP aggr-max (val-column-ref "Scores.Points")))
               FROM   (NAMED (list-ref tables 0))
               WHERE  (TRUE)
               GROUP-BY (list "Scores.StudentID")         
               HAVING (TRUE))
              ["t1" (list "StudentID" "Points")])
          (AS (SELECT (VALS (VAL-UNOP aggr-max (val-column-ref "Scores.Points")))
               FROM (NAMED (list-ref tables 0))
               WHERE (TRUE)
               GROUP-BY (list)
               HAVING (TRUE))
              ["t2" (list "MaxPoints")]))
   WHERE (BINOP "t1.Points" = "t2.MaxPoints")))

(define ros-instance (list q (list scores-info students-info) (list) prop-table-empty)) 