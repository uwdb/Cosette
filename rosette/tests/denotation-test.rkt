#lang rosette

(require "../sql.rkt" "../evaluator.rkt" "../denotation.rkt" "../table.rkt" "../syntax.rkt")

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
    (cons (list 2 1 3) 3)
    (cons (list 3 4 9) 0)))

(define content-d
  (list
    (cons (list 1 2 3) 2)
    (cons (list 2 3 3) 3)))

(define content-ab
  (list (cons (list 1 1 2 2 1 0) 6)))

(define content-c (list))

(define list2d 
  (list (list 1 2 3)
        (list 4 5 6)
        (list 7 8 9)
        (list 3 5 6)))

(define table1 (Table "t1" '("a" "b" "c") content-b))

(define q                                                                                                                                                     
  (query-aggr-general 
    (query-named table1) 
    (filter-true)
    (list "t1.a" "t1.b") 
    (list (val-group-by-col "t1.a") 
          (val-group-by-col "t1.b") 
          (val-uexpr aggr-sum (val-bexpr + (val-column-ref "t1.b") (val-column-ref "t1.c"))) 
          (val-uexpr aggr-min (val-uexpr (lambda (x) (+ x 100)) (val-column-ref "t1.c"))) 
          (val-uexpr aggr-sum (val-column-ref "t1.c")))
    (filter-true)))

(define q-macro
  (SELECT (VALS (val-group-by-col "t1.a") 
                (val-group-by-col "t1.b") 
                (VAL-UNOP aggr-sum (VAL-BINOP "t1.b" + "t1.c")) 
                (VAL-UNOP aggr-min (VAL-UNOP (lambda (x) (+ x 100)) "t1.c"))
                (VAL-UNOP aggr-sum "t1.c"))
   FROM (NAMED table1)
   WHERE (TRUE)
   GROUP-BY '("t1.a" "t1.b")
   HAVING (TRUE)))


(define q2                                                                                                                                                    
  (query-aggr-general 
    (query-named table1)
    (filter-true)
    (list) 
    (list (val-group-by-col "t1.a") 
          (val-group-by-col "t1.b") 
          (val-uexpr aggr-sum (val-bexpr + (val-column-ref "t1.b") (val-column-ref "t1.c"))) 
          (val-uexpr aggr-min (val-uexpr (lambda (x) (+ x 100)) (val-column-ref "t1.c"))) 
          (val-uexpr aggr-sum (VAL "t1.c")))
    (filter-true)))

(define q2-macro
  (SELECT (VALS (val-group-by-col "t1.a") 
                (val-group-by-col "t1.b") 
                (VAL-UNOP aggr-sum (VAL-BINOP "t1.b" +  "t1.c")) 
                (VAL-UNOP aggr-min (VAL-UNOP (lambda (x) (+ x 100))  "t1.c")) 
                (VAL-UNOP aggr-sum (val-column-ref "t1.c")))
   FROM (NAMED table1)
   WHERE (TRUE)
   GROUP-BY '()
   HAVING (TRUE)))


(define q3                                                                                                                                                    
  (query-aggr-general 
    (query-named table1) 
    (filter-binop < (val-column-ref "t1.c") (val-const 3))
    (list "t1.a" "t1.b") 
    (list (val-group-by-col "t1.a") 
          (val-group-by-col "t1.b") 
          (val-uexpr aggr-sum (val-bexpr + (val-column-ref "t1.b") (val-column-ref "t1.c"))) 
          (val-uexpr aggr-min (val-uexpr (lambda (x) (+ x 100)) (val-column-ref "t1.c"))) 
          (val-uexpr aggr-sum (val-column-ref "t1.c")))
    (filter-binop < (val-uexpr aggr-min (val-uexpr (lambda (x) (+ x 100)) (val-column-ref "t1.c"))) (val-const 105))))

(define q3-macro
  (SELECT (VALS (val-group-by-col "t1.a") 
                (val-group-by-col "t1.b") 
                (VAL-UNOP aggr-sum (VAL-BINOP "t1.b" + "t1.c"))
                (VAL-UNOP aggr-min (VAL-UNOP (lambda (x) (+ x 100)) "t1.c"))
                (VAL-UNOP aggr-sum "t1.c"))
   FROM (NAMED table1)
   WHERE (BINOP "t1.c" < 3)
   GROUP-BY (list "t1.a" "t1.b")
   HAVING (BINOP (VAL-UNOP aggr-min (VAL-UNOP (lambda (x) (+ x 100)) "t1.c")) < 105)))

(define b_plus (broad-casting-bexpr-wrapper +))

(b_plus 1 2)
(b_plus '((1 . 2) (3 . 5)) 2)
(b_plus '((1 . 2) (3 . 5)) '((9 . 2) (11 . 5)))

table1
(println "q1")
(denote-and-run q)
(denote-and-run q-macro)

(println "q2")
(denote-and-run q2)
(denote-and-run q2-macro)

(println "q3")
(denote-and-run q3)
(denote-and-run q3-macro)
