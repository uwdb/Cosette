;//http://stackoverflow.com/questions/39957816/get-unique-values-in-table-by-multiple-criteria

#lang rosette 
 
(require "../table.rkt" "../cosette.rkt" "../util.rkt" "../denotation.rkt" "../cosette.rkt" "../sql.rkt" "../evaluator.rkt" "../syntax.rkt" "../symmetry.rkt" "../test-util.rkt") 

(current-bitwidth #f)

(define s-info (table-info "s" (list "unknowns")))
 
(define r-info (table-info "r" (list "unknowns")))
 

(define (q1 tables) 
  (SELECT (VALS "x.unknowns") 
  FROM (AS (UNION-ALL (NAMED (list-ref tables 1)) (NAMED (list-ref tables 0))) ["x"]) 
  WHERE (TRUE)))

(define (q2 tables) 
  (UNION-ALL (SELECT (VALS "x.unknowns") 
  FROM (AS (NAMED (list-ref tables 1)) ["x"]) 
  WHERE (TRUE)) (SELECT (VALS "y.unknowns") 
  FROM (AS (NAMED (list-ref tables 0)) ["y"]) 
  WHERE (TRUE))))

(define ros-instance (list q1 q2 (list s-info r-info)))

(run-experiment ros-instance #f #f #f)
