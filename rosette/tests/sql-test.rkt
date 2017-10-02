#lang rosette

(require "../util.rkt" "../table.rkt" "../sql.rkt" "../evaluator.rkt" "../equal.rkt")


(define test-table1
  (list
    (cons (list 1 1 2) 2)
    (cons (list 1 1 2) 2)
    (cons (list 0 1 2) 2)
    (cons (list 1 2 1) 1)
    (cons (list 1 2 3) 1)
    (cons (list 2 1 0) 3)))
(define table1 (Table "t1" (list "c1" "c2" "c3") test-table1))

(define q (query-select 
            (list (val-column-ref "t1.c1") (val-column-ref "t1.c2"))
            (query-named table1)
            (filter-binop < (val-column-ref "t1.c1") (val-column-ref "t1.c2"))))

(define q2 (query-rename-full (query-named table1) "qt" (list "c12" "c22" "c32")))

(define q3 (query-join (query-named table1) (query-rename-full (query-named table1) "t2" (list "c1" "c2" "c3"))))

(define part-of-q3 (query-rename-full (query-named table1) "t2" (list "c1" "c2" "c3")))
