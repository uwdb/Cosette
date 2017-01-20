#lang rosette

(require "../util.rkt" "../table.rkt" "../sql.rkt" "../evaluator.rkt" "../equal.rkt")

(define t1 (Table "t1" (list "c1" "c2" "c3") (gen-sym-schema 3 2)))
; (define t1 (Table "t1" (list "c1" "c2" "c3") concrete-table-3-col))

(define subq-aggr-1
  (SELECT-DISTINCT (VALS "t1.c1" (AGGR aggr-sum 
			      (SELECT (VALS "t2.c6")
				 FROM (AS (NAMED t1) ["t2" (list "c4" "c5" "c6")])
				 WHERE (BINOP "t2.c4" = "t1.c1"))))
     FROM (NAMED t1)
     WHERE (filter-empty)))

(define subq-aggr-2
  (SELECT-DISTINCT (VALS "t1.c1" 
			 (AGGR aggr-sum
			       (SELECT (VALS "t4.c3")
				  FROM (AS (SELECT-DISTINCT (VALS "t2.c1" "t2.c2" 
								  (AGGR aggr-sum 
									(SELECT (VALS "t3.c3")
									   FROM (AS (NAMED t1) ["t3" (list "c1" "c2" "c3")])
									   WHERE (AND (BINOP "t3.c1" = "t2.c1") (BINOP "t3.c2" = "t2.c2")))))
							FROM (AS (NAMED t1) ["t2" (list "c1" "c2" "c3")])
						       WHERE (BINOP "t2.c1" = "t1.c1")) ["t4" (list "c1" "c2" "c3")])
				  WHERE (filter-empty))))
    FROM (NAMED t1)
    WHERE (filter-empty)))

(define subq-aggr-wrong-2
    (SELECT-DISTINCT (VALS "t1.c1" (AGGR aggr-sum
					 (SELECT-DISTINCT (VALS (AGGR aggr-sum 
								      (SELECT (VALS "t3.c3")											  						     
                                              FROM (AS (NAMED t1) ["t3" (list "c1" "c2" "c3")])
                                              WHERE (AND (BINOP "t3.c1" = "t2.c1") (BINOP "t3.c2" = "t2.c2")))))
                                      FROM (AS (NAMED t1) ["t2" (list "c1" "c2" "c3")])
                                      WHERE (BINOP "t2.c1" = "t1.c1"))))
                     FROM (NAMED t1)
                     WHERE (filter-empty)))

(define part-ag2 
  (SELECT-DISTINCT (VALS "t2.c1" "t2.c2" 
			(AGGR aggr-sum 
			     (SELECT (VALS "t3.c3")
				FROM (AS (NAMED t1) ["t3" (list "c1" "c2" "c3")])
				WHERE (AND (BINOP "t3.c1" = "t2.c1") (BINOP "t3.c2" = "t2.c2")))))
	    FROM (AS (NAMED t1) ["t2" (list "c1" "c2" "c3")])
	   WHERE (filter-empty)))

(define part-ag22 (SELECT-DISTINCT (VALS "t2.c1" "t2.c2" "t2.c3")
		 FROM (AS (NAMED t1) ["t2" (list "c1" "c2" "c3")])
		WHERE (filter-empty)))

;(run subq-aggr-2)
;(run subq-aggr-1)

; commutativity of selection query 1

; commutativity of selection query 2

(assert (sym-tab-constrain (Table-content t1)))
(define model (time (verify (same subq-aggr-1 subq-aggr-2))))
(define model2 (verify (same subq-aggr-1 subq-aggr-wrong-2)))

;model
model2

;(evaluate t1 model2)
;(evaluate (run subq-aggr-1) model2)
;(evaluate (run subq-aggr-wrong-2) model2)
;(println "========")
;(println "========")
;(denote-sql subq-aggr-1 (make-hash))

;(evaluate (Table-content t1) model)
;(evaluate (run subq-aggr-1) model)
;(evaluate (run subq-aggr-2) model)
;(evaluate (run part-ag2) model)
;(evaluate (run part-ag22) model)
