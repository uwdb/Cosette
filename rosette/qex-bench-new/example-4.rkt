#lang rosette

(current-bitwidth 10)

(require "../cosette.rkt" "../util.rkt" "../denotation.rkt" 
         "../sql.rkt" "../evaluator.rkt" "../syntax.rkt" "../symmetry.rkt") 

(provide ros-instance)

(define scores-info (table-info "Scores" (list "StudentID" "CourseID" "Points")))
(define students-info (table-info "Students" (list "StudentNr" "StudentName")))

; DECLARE @x as tinyint;
; SELECT DISTINCT Scores.StudentID, SUM(Scores.Points)
; FROM Scores
; WHERE Scores.Points > 2
; HAVING SUM(Scores.Points) >= @x AND @x > 5

(define-symbolic* x integer?)

(define (q tables)
   (SELECT-DISTINCT (VALS "t.StudentID" "t.Points")
    FROM (AS (SELECT (VALS "Scores.StudentID" (VAL-UNOP aggr-sum (val-column-ref "Scores.Points")))
              FROM   (NAMED (list-ref tables 0))
              WHERE (BINOP "Scores.Points" > 2)
              GROUP-BY (list)         
              HAVING (AND (AND (BINOP (VAL-UNOP aggr-sum (val-column-ref "Scores.Points")) > x) 
                               (BINOP x > 5))
                          (BINOP (COUNT-DISTINCT "Scores.StudentID" > 3))))
       ["t" (list "StudentID" "Points")])
    WHERE (TRUE)))

(define ros-instance (list q (list scores-info students-info) (list x) prop-table-empty)) 
