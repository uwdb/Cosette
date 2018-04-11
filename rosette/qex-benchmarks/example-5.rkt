#lang rosette

(current-bitwidth 10)

(require "../cosette.rkt" "../util.rkt" "../denotation.rkt" 
         "../sql.rkt" "../evaluator.rkt" "../syntax.rkt" "../symmetry.rkt") 

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
      (cosette-check-output-prop q tables (list) prop-table-empty)))

(time (test-now ros-instance m-tables))
;(time (test-now ros-instance tables))