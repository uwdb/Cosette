#lang rosette

(require "../util.rkt" "../table.rkt" "../sql.rkt" "../evaluator.rkt" "../equal.rkt")

(define t1 (Table "votes" (list "vote" "story_id") (gen-sym-schema 2 3)))
(define t2 (Table "stories" (list "id") (gen-sym-schema 1 2)))

(define st1 (Table "votes" (list "vote" "story_id" "aggrf") (gen-sym-schema 3 2)))
(define ct 
  (Table "votes" (list "vote" "story_id" "aggrf") 
         (list (cons (list 2 3 1) 2)
               (cons (list 1 3 3) 1)
               (cons (list 1 3 4) 3)
               (cons (list 2 3 2) 1))))

(define ct1 
  (Table "votes" (list "vote" "story_id") 
         (list (cons (list 2 3) 2)
               (cons (list 1 3) 1)
               (cons (list 2 1) 3))))

(define ct2 
  (Table "stories" (list "id") 
         (list (cons (list 2) 1)
               (cons (list 3) 1))))


(define t3 (Table "t" (list "sum") (list (cons (list -2) 1))))
(define t4 (Table "t" (list "sum") (list)))

(define test-q
  (SELECT-GROUP (NAMED st1) (list "votes.vote" "votes.story_id") aggr-sum "votes.aggrf"))

(define test-q2
  (SELECT-GROUP-SUBQ (NAMED st1) (list "votes.vote" "votes.story_id") aggr-sum "votes.aggrf"))


;(writeln (denote-sql test-q (make-hash)))

;(run test-q)
;(run test-q2)
;(time (verify (same test-q test-q2)))

;(define t2 (Table "t1" (list "id") (list (cons (list 0) 0))))

; SELECT SUM(vote) AS sumv FROM votes AS v INNER JOIN stories AS s ON v.story_id = s.id;

(define q1
  (SELECT (VALS (AGGR aggr-sum (SELECT (VALS "v.vote")
                                       FROM   (JOIN (AS (NAMED t1) ["v" (list "vote" "story_id")]) 
                                                    (AS (NAMED t2) ["s" (list "id")]))
                                       WHERE (BINOP "v.story_id" = "s.id"))))
          FROM (NAMED t3)
          WHERE (F-EMPTY)))

(define q2 (SELECT (VALS (VAL-BINOP 12 * "t.sum") 1) FROM (NAMED t3) WHERE (F-EMPTY)))

(define q3 
  (SELECT (VALS "j.s1")
          FROM (AS (JOIN q1 q2)
                   ["j" (list "s1" "s2")])
          WHERE (BINOP "j.s1" > "j.s2")))

(define q4 (NAMED t4))

(run q2)
;(get-content (run q2))
;(get-content (run q3))
;(get-content (run q4))

;(time (verify (same q3 q4)))
;(time (verify (neq q3 q4)))

