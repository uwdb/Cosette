#lang rosette

(current-bitwidth 10)

(require "../cosette.rkt" "../util.rkt" "../denotation.rkt" 
         "../sql.rkt" "../evaluator.rkt" "../syntax.rkt" "../symmetry.rkt") 

(provide ros-instance)

(define scores-info (table-info "Scores" (list "StudentID" "CourseID" "Points")))
(define students-info (table-info "Students" (list "StudentNr" "StudentName")))

; DECLARE @x as tinyint;
; SELECT DISTINCT COUNT(S.StudentName)
; FROM Students as S
; WHERE S.StudentName LIKE "%Mar[gkc]us%" AND S.StudentNr > @x
; HAVING COUNT(S.StudentName) > @x AND @x > 2

(define-symbolic* x integer?)

(define (q tables)
   (SELECT-DISTINCT (VALS "t.StudentNameCount")
    FROM (AS (SELECT (VALS (VAL-UNOP aggr-count (val-column-ref "Students.StudentName")))
              FROM   (NAMED (list-ref tables 1))
              WHERE (BINOP "Students.StudentNr" > x)
              GROUP-BY (list)         
              HAVING (AND (BINOP (VAL-UNOP aggr-count (val-column-ref "Students.StudentName")) > x) 
                          (BINOP x > 2)))
       ["t" (list "StudentNameCount")])
    WHERE (TRUE)))

(define ros-instance (list q (list scores-info students-info) (list x) prop-table-empty))