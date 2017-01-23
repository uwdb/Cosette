#lang rosette 

(require "../equal.rkt" "../syntax.rkt" "../denotation.rkt" "../table.rkt")

(provide 
  sym-table-gen)

(define (sv)
   (define-symbolic* y integer?) ; creates a different constant when evaluated
    y)

(define sym-content
  (list 
    (cons (list (sv) (sv) (sv) (sv) (sv) (sv)) (sv))
    (cons (list (sv) (sv) (sv) (sv) (sv) (sv)) (sv))
    (cons (list (sv) (sv) (sv) (sv) (sv) (sv)) (sv))
    (cons (list (sv) (sv) (sv) (sv) (sv) (sv)) (sv))
    (cons (list (sv) (sv) (sv) (sv) (sv) (sv)) (sv))
    (cons (list (sv) (sv) (sv) (sv) (sv) (sv)) (sv))
    (cons (list (sv) (sv) (sv) (sv) (sv) (sv)) (sv))
    (cons (list (sv) (sv) (sv) (sv) (sv) (sv)) (sv))
    (cons (list (sv) (sv) (sv) (sv) (sv) (sv)) (sv))
    (cons (list (sv) (sv) (sv) (sv) (sv) (sv)) (sv))
    (cons (list (sv) (sv) (sv) (sv) (sv) (sv)) (sv))
    (cons (list (sv) (sv) (sv) (sv) (sv) (sv)) (sv))
    (cons (list (sv) (sv) (sv) (sv) (sv) (sv)) (sv))))

(define (sym-table-gen num-col num-unique-rows)
  (let ([gen-list (lambda (proc n)
                    (map (lambda (x) (proc)) (range n)))])
    (gen-list (lambda ()
                (cons (gen-list sv num-col) (sv)))
              num-unique-rows)))

; the running part
; (define q1 (list-ref queries 0))
; (define q2 (list-ref queries 1))
; (define q3 (list-ref queries 2))

; (define (same content)
;  (assert (eq? (q1 content) (q3 content))))

; (define cex (verify (same sym-content)))

; (println (q1 test-table))
; (println (q2 test-table))
; (println (q3 test-table))

; (evaluate sym-content cex)
; (verify (same sym-content))

(define table-content
      (list
	      (cons (list 1 1 2) 2)
	            (cons (list 1 1 2) 2)
		          (cons (list 0 1 2) 2)
			        (cons (list 1 2 1) 1)
				      (cons (list 1 2 3) 1)
				            (cons (list 2 1 0) 3)))

(define symbolic-table (Table "t1" (list "c1" "c2" "c3") sym-content))

(define try-symbolic-0
    (SELECT (VALS "t1.c1" "t1.c2" "t1.c3")
       FROM   (NAMED symbolic-table)	          
      WHERE  (AND (BINOP "t1.c1" < "t1.c2") (BINOP "t1.c1" < "t1.c2"))))

(define try-symbolic-1
    (SELECT (VALS "t1.c1" "t1.c2" "t1.c3")
	       FROM   (NAMED symbolic-table)
	          WHERE  (AND (BINOP "t1.c1" < "t1.c2") (BINOP "t1.c1" < "t1.c3"))))

(define try-symbolic-2
    (SELECT (VALS "t1.c1" "t1.c2" "t1.c3")
      FROM   (NAMED symbolic-table)
      WHERE  (AND (BINOP "t1.c1" < "t1.c3") (BINOP "t1.c1" < "t1.c2"))))

(println " --------------- ")

(define try-symbolic-3
  (NAMED symbolic-table))

(define try-symbolic-4
  (NAMED symbolic-table))

(define (same1)
  (assert (eq? (get-content (run try-symbolic-1)) (get-content (run try-symbolic-2)))))

(define (same-func q1 q2)
  (assert (bag-equal (get-content (run q1)) (get-content (run q2)))))

(println " --------------- ")

(define (same)
  (assert (equal? (run try-symbolic-1) (run try-symbolic-2))))

; (run try-symbolic-1)
; (run try-symbolic-2)

;(define cex (verify (same)))
;(evaluate sym-content cex)
(verify (same1))
(verify (same-func try-symbolic-0 try-symbolic-1))
(verify (same-func try-symbolic-3 try-symbolic-4))

; (define (simple-same) (assert (eq? sym-content sym-content)))
; (verify (simple-same))
;; (define cex (verify (same)))
;; (evaluate sym-content cex)
