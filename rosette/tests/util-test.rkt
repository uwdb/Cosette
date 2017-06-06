#lang rosette

(require "../util.rkt" "../table.rkt" "../sql.rkt" "../evaluator.rkt" "../equal.rkt")

(current-bitwidth 5)

(define st (Table "votes" (list "vote" "story_id" "aggrf") (gen-sym-schema 3 2)))

;; test ordered

(define (test-q t)
  (SELECT-GROUP (NAMED t) (list "votes.vote" "votes.story_id") aggr-sum "votes.aggrf"))

(define (test-q2 t)
  (SELECT-GROUP-SUBQ (NAMED t) (list "votes.vote" "votes.story_id") aggr-sum "votes.aggrf"))

(time (verify (same (test-q st) (test-q2 st))))

(time (verify
        #:assume (begin
                   (assert-table-ordered st)
                   (assert-table-cols-distinct st 1))
        #:guarantee (same (test-q st) (test-q2 st))))


;;; testing assert-table-col-distinct constraint
(define (test-2-q t)
  (SELECT-GROUP (NAMED t) (list "votes.story_id") aggr-sum "votes.aggrf"))

(define (test-2-q2 t)
  (SELECT (VALS "votes.story_id" "votes.aggrf") FROM (NAMED t) WHERE (F-EMPTY)))

(time (verify
        #:assume (begin (assert-table-ordered st))
        #:guarantee (same (test-2-q st) (test-2-q2 st))))

(time (verify
        #:assume (begin
                   (assert-table-ordered st)
                   (assert-table-col-distinct st (list 1)))
        #:guarantee (same (test-2-q st) (test-2-q2 st))))

;(let* ([ct (evaluate st cex)]
;       [t1 (run (test-q ct))]
;       [t2 (run (test-q2 ct))])
;  (println (bag-equal (get-content t1) (get-content t2)))
;  (println (table-content-ascending? (get-content ct))))
