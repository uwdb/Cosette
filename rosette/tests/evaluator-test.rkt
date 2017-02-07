#lang rosette

(require "../evaluator.rkt")

;; test list-distinct function
(assert (list-distinct? '(1 3 5 6 2 4 7)))
(assert (list-distinct? '(1)))
(assert (list-distinct? '()))
(assert (not (list-distinct? '(1 3 1 6 2 4 7))))
(assert (not (list-distinct? '(8 8 8 8 8))))

;; several test xproduct
(define content-a
  (list
    (cons (list 1 1 2) 2)
    (cons (list 0 1 2) 2)))

(define content-b
  (list
    (cons (list 1 2 3) 1)
    (cons (list 1 2 4) 2)
    (cons (list 2 1 0) 3)
    (cons (list 1 2 1) 3)
    (cons (list 2 1 3) 3)))

(define content-d
  (list
    (cons (list 1 2 3) 2)
    (cons (list 2 3 3) 3)))

(define content-ab
  (list (cons (list 1 1 2 2 1 0) 6)))

(define content-c (list))

; tests
; (time (println (raw-aggr content-b (list 0 1) raw-aggr-sum 2)))
; (println (xproduct-raw content-a content-b))
; (println (get-content (left-outer-join table-a table-b 2 2)))
; (left-outer-join-raw content-c content-c 0 0 3 3)


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
