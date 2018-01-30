#lang rosette 
 
(require "../cosette.rkt" "../util.rkt" "../denotation.rkt" "../cosette.rkt" "../sql.rkt" "../evaluator.rkt" "../syntax.rkt" "../symmetry.rkt" "../test-util.rkt") 
  
(current-bitwidth #f)
 
(define-symbolic div_ (~> integer? integer? integer?))
 
(define t-info (table-info "t" (list "id" "sal")))
 

(define (q1 k tables) 
  (SELECT (VALS "x.id" (VAL-UNOP aggr-sum (val-column-ref "x.sal"))) 
 FROM (AS (NAMED (list-ref tables 0)) ["x"]) 
 WHERE (TRUE) GROUP-BY (list "x.id") 
 HAVING (BINOP (VAL-UNOP aggr-count-distinct (val-column-ref "x.sal")) > k)))

(define (q2 k tables) 
  (SELECT (VALS "x.id" (VAL-UNOP aggr-sum (val-column-ref "x.sal"))) 
 FROM (AS (NAMED (list-ref tables 0)) ["x"]) 
 WHERE (TRUE) GROUP-BY (list "x.id") 
 HAVING (BINOP (VAL-UNOP aggr-count-distinct (val-column-ref "x.sal")) > (+ 1 k))))

(define ros-instance (list q1 q2 (list t-info)))

(for ([k (list 1 2 3 4 5 6 7 8 9 10)])
  (let ([ros-instance (list (lambda (x) (q1 k x)) (lambda (x) (q2 k x)) (list t-info))])
    (run-experiment ros-instance)))
 
;(run-experiment ros-instance)

