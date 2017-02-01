#lang rosette                                                                                                                                                 

(require "../util.rkt" "../sql.rkt" "../table.rkt"  "../evaluator.rkt" "../equal.rkt")

(define symbolic-t1 (Table "t1" (list "c1" "c2" "c3") (gen-sym-schema 3 2)))    
(define symbolic-t2 (Table "t2" (list "c4" "c5" "c6") (gen-sym-schema 3 2)))    

(define q1
    (SELECT (VALS "t1.c1" "t1.c2" "t1.c3" "t3.c4" "t3.c5" "t3.c6")
       FROM (JOIN (NAMED symbolic-t1) 
		   (AS (SELECT  (VALS "t2.c4" "t2.c5" "t2.c6")
			FROM  (NAMED symbolic-t2)
			WHERE (AND (BINOP "t2.c5" >= "t2.c4") (BINOP "t2.c5" <= "t2.c6"))) ["t3" (list "c4" "c5" "c6")]))
      WHERE (BINOP "t1.c1" eq? "t3.c4")))

(define q2
  (SELECT (VALS "t1.c1" "t1.c2" "t1.c3" "t2.c4" "t2.c5" "t2.c6")
     FROM (JOIN (NAMED symbolic-t1) (NAMED symbolic-t2))
    WHERE (AND (BINOP "t1.c1" eq? "t2.c4") (AND (BINOP "t2.c5" >= "t2.c4") (BINOP "t2.c5" <= "t2.c6")))))

;; (run q1)
;; (run q2)

(time (verify (same q1 q2)))
