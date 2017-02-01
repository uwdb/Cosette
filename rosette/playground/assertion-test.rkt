#lang rosette

(require "../util.rkt" "../table.rkt" "../sql.rkt" "../evaluator.rkt" "../equal.rkt")

(current-bitwidth 2)

(define st (Table "votes" (list "vote" "story_id" "aggrf") (gen-sym-schema 3 3)))
(define ct 
  (Table "votes" (list "vote" "story_id" "aggrf") 
         (list (cons (list -16 -16 -16) 1)
               (cons (list 15 14 15) 8))))

(define t3 (Table "t" (list "sum") (list (cons (list -2) 1))))
(define t4 (Table "t" (list "sum") (list)))

(define (test-q t)
  (SELECT-GROUP (NAMED t) (list "votes.vote" "votes.story_id") aggr-sum "votes.aggrf"))

(define (test-q2 t)
  (SELECT-GROUP-SUBQ (NAMED t) (list "votes.vote" "votes.story_id") aggr-sum "votes.aggrf"))

;(writeln (denote-sql test-q (make-hash)))

;(time (verify (assert-table-ordered st)))

(time (verify (same (test-q st) (test-q2 st))))

(time (verify
        #:assume (assert-table-ordered st)
        #:guarantee (same (test-q st) (test-q2 st))))

;(let* ([ct (evaluate st cex)]
;       [t1 (run (test-q ct))]
;       [t2 (run (test-q2 ct))])
;  (println (bag-equal (get-content t1) (get-content t2)))
;  (println (table-content-ascending? (get-content ct))))
