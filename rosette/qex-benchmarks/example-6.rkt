#lang rosette

(current-bitwidth 10)

(require "../cosette.rkt" "../util.rkt" "../denotation.rkt" 
         "../sql.rkt" "../evaluator.rkt" "../syntax.rkt" "../symmetry.rkt") 

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

(define ros-instance (list q (list scores-info students-info))) 
(define table-info-list (last ros-instance))
(define table-size-list (make-list (length table-info-list) 10))
(define empty-tables (init-sym-tables table-info-list (build-list (length table-info-list) (lambda (x) 0))))
(define tables (init-sym-tables-from-func table-info-list table-size-list gen-qex-sym-schema))

(define qt (q empty-tables))

(define mconstr (big-step (init-constraint qt) 20))

;(define m-tables (init-sym-tables-from-func table-info-list table-size-list gen-sym-schema))
(define m-tables (init-sym-tables-from-func table-info-list table-size-list gen-qex-sym-schema))
(assert-sym-tables-mconstr m-tables (go-break-symmetry-single qt))

(define (test-now instance tables)
    (let* ([q ((list-ref instance 0) tables)])
      ;(println tables)
      (cosette-check-output-prop q tables (list x) prop-table-empty)))

;(time (test-now ros-instance m-tables))
(time (test-now ros-instance tables))