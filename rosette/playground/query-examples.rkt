#lang rosette

(require "evaluator.rkt")

(provide queries test-table test-table1)

(define test-table
  (list
    (cons (list 1 1 2) 2)
    (cons (list 0 1 2) 2)	          
    (cons (list 1 2 1) 1)
    (cons (list 2 1 0) 3)))

(define test-table1
  (list
    (cons (list 1 1 2) 2)
    (cons (list 1 1 2) 2)
    (cons (list 0 1 2) 2)	          
    (cons (list 1 2 1) 1)
    (cons (list 1 2 3) 1)
    (cons (list 2 1 0) 3)))

; SELECT *
; FROM table
; WHERE c0 < c1 
;	AND c1 < c2 
(define q1 (lambda (content) 
     (filter 
	(lambda (t) 
	  (let ([ct (car t)])
	    (and 
	      (< (list-ref ct 0) (list-ref ct 1))
	      (< (list-ref ct 1) (list-ref ct 2))))) 
	content))
  )

; SELECT *
; FROM table
; WHERE c1 < c2
; 	AND c1 >= c0
(define q2 
  (lambda (content)
     (filter 
       (lambda (t) 
	 (let ([ct (car t)])
	   (and 
	     (< (list-ref ct 1) (list-ref ct 2))
	     (>= (list-ref ct 1) (list-ref ct 0)))))
       content))
  )

(define (flatten-once lst)
      (apply append lst))

; subquery:
; SELECT c2
; FROM table
; WHERE c0 = [0]
; 	AND c1 = [1]
(define q3-subquery
  (lambda (content c0 c1)
    (projection
      (list 2)
      (filter 
      	(lambda (t)
	  (let ([ct (car t)])
	    (and 
	      (eq? (list-ref ct 0) c0)
	      (eq? (list-ref ct 1) c1))))
      content))))

; SELECT DISTINCT c1, c2, MAX(subquery)
(define q3
  (lambda (content)
    (dedup 
      (map (lambda (p)
	(cons 
	  (append 
	    (list (caar p) (cadar p)) 
	    (list 
	      (apply 
		max 
		(flatten-once 
		  (map (lambda (t) (car t))
		       (q3-subquery content (list-ref (car p) 0) (list-ref (car p) 1))))))) 
	    (cdr p)))
	content))))

(define queries (list q1 q2 q3))
 
; (q3 test-table1)

; (apply max (flatten-once (map (lambda (t) (car t)) (q3-subquery test-table1 1 2))))

; SELECT t1.c1, MAX(SELECT t2.c2 FROM table1 AS t2[c1,c2] WHERE t2.c1 = t1.c1)
; FROM table1 AS t1[c1,c2]
; WHERE c1 > 1

;(SELECT 
;  (t1.c1 (MAX (SELECT (t2.c2) (table1 AS t2) (t2.c1 == t1.c1))))
;  (FROM table1 AS t1)
;  (WHERE t1.1 > 1))

;(define test-query-001
;  (query-select
;    `(,(val-column-ref "t1.c1") 
;      ,(val-agg agg-max 
;	        (query-select 
;		  `((val-column-ref "t2.c2"))
;		  (query-rename (query-named table1) "t2" `("c1" "c2" "c3")))))))

; commutativity of selection query 1
(define selection-commute-q1
  (SELECT (VALS "t1.c1" "t1.c2" "t1.c3")
          FROM  (AS (SELECT (VALS "t1.c1" "t2.c2" "t1.c3")
                                FROM (NAMED t1)
                                WHERE "t1.c1" < "t1.c2")
                    ["t2", '("c1", "c2", "c3")])
          WHERE  (BINOP "t2.c1" < "t1.c3")))

; commutativity of selection query 2
(define selection-commute-q2
    (SELECT (VALS "t1.c1" "t1.c2" "t1.c3")
	       FROM   (NAMED t1)
	          WHERE  (AND (BINOP "t1.c1" < "t1.c2") (BINOP "t1.c1" < "t1.c3"))))
