#lang rosette

(require "../util.rkt" "../sql.rkt" "../table.rkt"  "../evaluator.rkt" "../equal.rkt"  rosette/lib/synthax)

; ------- actual tables (only for test) -------

(define c-course
  (Table "c" (list "cid" "dept")
         (list
          (cons (list 0 1) 8)
          (cons (list 2 2) 15))))

(define c-takes
  (Table "d" (list "id" "cid")
         (list
          (cons (list 2 2) 2))))

; ------------ symbolic tables ----------------
; we need at least two rows

(define s-course (Table "c" (list "cid" "dept") (gen-sym-schema 2 1)))

(define s-takes (Table "d" (list "id" "cid") (gen-sym-schema 2 1)))

; ------------ count bug ----------------------
(define course s-course)
(define takes s-takes)

;SELECT dept, COUNT(DISTINCT id) FROM
;course LEFT OUTER JOIN takes
;USING(course_id) GROUP BY dept name

(define q1
   (AS
     (SELECT (VALS "t.cid1" "t.dept" "t.id" "t.cid2")
	     FROM  (AS (JOIN (NAMED course) (NAMED takes))
		       ["t" (list "cid1" "dept" "id" "cid2")])
	     WHERE (BINOP "t.cid1" equal? "t.cid2"))
     ["t" (list "cid1" "dept" "id" "cid2")]))

(define q2
  (SELECT-DISTINCT (VALS "t.dept" 
			 (AGGR-SUBQ aggr-count
			       (SELECT-DISTINCT (VALS "t0.cid1")
					   FROM (AS q1 ["t0" (list "cid1" "dept" "id" "cid2")])
					  WHERE (BINOP "t0.dept" equal? "t.dept"))))
		FROM q1
		WHERE (TRUE)))


; === mutant 1 === (JOIN --> LEFT JOIN)

(define q3
   (AS
     (SELECT (VALS "t.cid1" "t.dept" "t.id" "t.cid2")
	     FROM  (AS (JOIN (NAMED course) (NAMED takes))
		       ["t" (list "cid1" "dept" "id" "cid2")])
	     WHERE (BINOP "t.cid1" equal? "t.cid2"))
     ["t" (list "cid1" "dept" "id" "cid2")]))

(define q4
  (AS 
    (LEFT-OUTER-JOIN (NAMED course) (NAMED takes) 
                     (BINOP "c.cid" equal? "d.cid"))
    ["t" (list "cid1" "dept" "id" "cid2")]))

(define q5
  (SELECT-DISTINCT (VALS "t.dept" 
			 (AGGR-SUBQ aggr-count
			       (SELECT-DISTINCT (VALS "t0.cid1")
					   FROM (AS q4 ["t0" (list "cid1" "dept" "id" "cid2")])
					  WHERE (BINOP "t0.dept" equal? "t.dept"))))
		FROM q4
		WHERE (TRUE)))

; === mutant 2 (aggregator mutant)

(define q6
  (SELECT-DISTINCT (VALS "t.dept" 
			 (AGGR-SUBQ aggr-count
			       (SELECT (VALS "t0.cid1")
					   FROM (AS q1 ["t0" (list "cid1" "dept" "id" "cid2")])
					  WHERE (BINOP "t0.dept" equal? "t.dept"))))
		FROM q1
		WHERE (TRUE)))

; === mutant 3 (aggregator mutant)

(define q7
  (SELECT-DISTINCT (VALS "t.dept" 
			 (AGGR-SUBQ aggr-sum
			       (SELECT-DISTINCT (VALS "t0.cid1")
					   FROM (AS q1 ["t0" (list "cid1" "dept" "id" "cid2")])
					  WHERE (BINOP "t0.dept" equal? "t.dept"))))
		FROM q1
		WHERE (TRUE)))
; expect model
;(run q2)
;(run q5)
;(run q6)
;(run q7)
(time (verify (same q2 q5)))
(time (verify (same q2 q6)))
(time (verify (same q2 q7)))
