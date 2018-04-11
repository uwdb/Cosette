#lang rosette

(current-bitwidth 10)

(require "../cosette.rkt" "../util.rkt" "../denotation.rkt" 
         "../sql.rkt" "../evaluator.rkt" "../syntax.rkt" "../symmetry.rkt") 

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

(define ros-instance (list q (list scores-info students-info))) 
(define table-info-list (last ros-instance))
(define table-size-list (make-list (length table-info-list) 3))
(define empty-tables (init-sym-tables table-info-list (build-list (length table-info-list) (lambda (x) 0))))
(define tables (init-sym-tables-from-func table-info-list table-size-list gen-qex-sym-schema))

(define qt (q empty-tables))

(define mconstr (big-step (init-constraint qt) 20))

;(define m-tables (init-sym-tables-from-func table-info-list table-size-list gen-sym-schema))
(define m-tables (init-sym-tables-from-func table-info-list table-size-list gen-qex-sym-schema))
(assert-sym-tables-mconstr m-tables (go-break-symmetry-single qt))

(define (test-now instance tables)
    (let* ([q ((list-ref instance 0) tables)])
      (cosette-check-output-prop q tables (list x) prop-table-empty)))

(time (test-now ros-instance m-tables))
;(time (test-now ros-instance tables))