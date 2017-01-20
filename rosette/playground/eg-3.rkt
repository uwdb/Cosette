#lang rosette

(require "../test-util.rkt" "../../table.rkt" "../../sql.rkt" "../../evaluator.rkt" "../../equal.rkt")

;(current-bitwidth 32)

(define (aggr-count l)
  (foldl + 0 (map cdr (get-content l))))

(define t (Table "t" (list "v") (gen-sym-schema 1 8)))
(define ct (Table "t" (list "v") (list (cons (list 1) 10) (cons (list 2) 12))))
(define t3 (Table "t" (list "v") (list (cons (list 50) 1))))
(define t4 (Table "t" (list "v") (list)))

;(define t2 (Table "t1" (list "id") (list (cons (list 0) 0))))

; SELECT SUM(vote) AS sumv FROM votes AS v INNER JOIN stories AS s ON v.story_id = s.id;

(define q1
	(SELECT-DISTINCT 
      (VALS (AGGR aggr-count (SELECT-DISTINCT (VALS "t.v") FROM (NAMED t) WHERE (filter-empty))))
	 FROM  (NAMED t3)
	 WHERE (filter-empty)))

(define cq1
	(SELECT-DISTINCT (VALS (AGGR aggr-count (SELECT-DISTINCT (VALS "t.v") FROM (NAMED ct) WHERE (filter-empty))))
	 FROM  (NAMED t3)
	 WHERE (filter-empty)))

(define q2
	(SELECT (VALS "j.s1")
     FROM (AS q1 ["j" (list "s1")])
    WHERE (BINOP "j.s1" < 8)))

(define cq2
	(SELECT (VALS "j.s1")
     FROM (AS cq1 ["j" (list "s1")])
    WHERE (BINOP "j.s1" < 50)))

(define q4 (NAMED t4))

;(run cq1)
;(run cq2)
;(run q4)

;(time (verify (same cq2 q4)))
;(time (verify (neq q2 q4)))
;(get-content (run q2))
;(get-content (run q3))
;(get-content (run q4))

(time (verify (same q2 q4)))
(time (verify (neq q2 q4)))

