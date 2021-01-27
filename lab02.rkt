; q1a
;;; SELECT 
;;;     cmte_id,
;;;     transaction_amt,
;;;     name
;;; FROM indiv_sample_nyc
;;; WHERE name LIKE '%TRUMP%' AND name LIKE '%DONALD%'
(define q1a
    (SELECT (VALS "indiv_sample_nyc.cmte_id" "indiv_sample_nyc.transaction_amt" "indiv_sample_nyc.name") 
     FROM (NAMED indiv_sample_nyc)
     WHERE (AND (LIKEOP "indiv_sample_nyc.name" "%DONALD%") 
                (LIKEOP "indiv_sample_nyc.name" "%TRUMP%"))
    ))


; q1b
;;; SELECT 
;;;     cmte_id,
;;;     transaction_amt,
;;;     name
;;; FROM indiv_sample_nyc
;;; WHERE name LIKE '%TRUMP%' AND name LIKE '%DONALD%' AND name NOT LIKE '%INC%'
(define q1b
    (SELECT (VALS "indiv_sample_nyc.cmte_id" "indiv_sample_nyc.transaction_amt" "indiv_sample_nyc.name") 
     FROM (NAMED indiv_sample_nyc)
     WHERE (AND (LIKEOP "indiv_sample_nyc.name" "%DONALD%")
                (AND (LIKEOP "indiv_sample_nyc.name" "%TRUMP%") 
                     (NOT (LIKEOP "indiv_sample_nyc.name" "%INC%"))))
    ))

; q1c
;;; SELECT 
;;;     cmte_id,
;;;     SUM(transaction_amt) as total_amount,
;;;     COUNT(*) as num_donations
;;; FROM indiv_sample_nyc
;;; WHERE name LIKE '%TRUMP%' AND name LIKE '%DONALD%' AND name NOT LIKE '%INC%'
;;; GROUP BY cmte_id
;;; ORDER BY total_amount DESC
(define q1c
    (AS 
    (SELECT (VALS "indiv_sample_nyc.cmte_id" (SUM "indiv_sample_nyc.transaction_amt") (COUNT *)) ; count(*) ??? value rename??
     FROM ( indiv_sample_nyc)
     WHERE (AND (LIKEOP "indiv_sample_nyc.name" "%DONALD%")
                (AND (LIKEOP "indiv_sample_nyc.name" "%TRUMP%") 
                     (NOTLIKEOP "indiv_sample_nyc.name" "%INC%")))
     GROUP-BY (list "indiv_sample_nyc.cmte_id")
     HAVING (TRUE)  
     ORDER-BY () ; missing command... test before ORDERING
    ) ["q1c" (list "cmte_id" "total_amount" "num_donations")]))

; q1d
;;; SELECT 
;;;     cmte_id,
;;;     SUM(transaction_amt) as total_amount,
;;;     COUNT(*) as num_donations,
;;;     cmte_nm
;;; FROM 
;;;         (SELECT *
;;;         FROM indiv_sample_nyc, comm
;;;         WHERE indiv_sample_nyc.cmte_id == comm.cmte_id)
;;; WHERE name LIKE '%TRUMP%' AND name LIKE '%DONALD%' AND name NOT LIKE '%INC%'
;;; GROUP BY cmte_id
;;; ORDER BY total_amount DESC
(define q1d
    (SELECT (VALS "t.cmte_id" (SUM "t.transaction_amt") (COUNT *) "t.cmte_nm") ; count(*) ??? value rename??
     FROM (AS (SELECT (*) ; SELECT * ?
               FROM (JOIN (NAMED indiv_sample_nyc) (NAMED comm))
               WHERE (BINOP "indiv_sample_nyc.cmte_id" = "comm.cmte_id"))
            ["t" (list "cmte_id" "transaction_amt" "cmte_nm")])
     WHERE (AND (LIKEOP "t.name" "%DONALD%")
                (AND (LIKEOP "t.name" "%TRUMP%") 
                     (NOTLIKEOP "t.name" "%INC%")))
     GROUP-BY (list "t.cmte_id") 
     HAVING (TRUE)
     ORDER-BY () ; missing command
    ))

; q2a
;;; SELECT
;;;     cmte_id AS committee_id,
;;;     sum(transaction_amt) AS total_amount,
;;;     count(*) AS count
;;; FROM indiv_sample_nyc
;;; WHERE cmte_id LIKE '%5'
;;; GROUP BY cmte_id
;;; ORDER BY count DESC
;;; LIMIT 5
(define q2a
    (SELECT (VALS "indiv_sample_nyc.cmte_id" (SUM "indiv_sample_nyc.transaction_amt") (COUNT *) "indiv_sample_nyc.cmte_nm") ; count(*) ??? value rename??
     FROM (NAMED indiv_sample_nyc)
     WHERE (LIKEOP "indiv_sample_nyc.cmte_id" "%5")
     GROUP-BY (list "indiv_sample_nyc.cmte_id") 
     HAVING (TRUE)
     ORDER-BY ()
     LIMIT (VAL 5) ; missing commmand
    )
)

; q2b
;;; SELECT c1.cand_name, c2.cmte_nm
;;; FROM cand c1 INNER JOIN comm c2 ON c1.cand_id = c2.cand_id
;;; ORDER BY c1.cand_name DESC
;;; LIMIT 5
(define q2b
    (SELECT (VALS "t.cand_cand_id" "t.comm_cmte_nm") 
     FROM (AS (JOIN (NAMED cand) (NAMED comm))
           ["t" (list "cand_cand_id" "comm_cand_id" "comm_cmte_nm")])
     WHERE (BINOP "t.cand_cand_id" = "t.comm_cand_id")
     ORDER-BY ()
     LIMIT (VAL 5)
    )
)



; q2c
;;; SELECT c1.cand_name, c2.cmte_nm
;;; FROM cand c1 LEFT OUTER JOIN comm c2 ON c1.cand_id = c2.cand_id
;;; ORDER BY c1.cand_name DESC
;;; LIMIT 5
(define q2c
    (SELECT (VALS "t.cand_cand_id" "t.comm_cmte_nm")
     FROM (AS (LEFT-OUTER-JOIN (NAMED cand) (NAMED comm) (BINOP "cand.cand_id" = "comm.cand_id"))
           ["t" (list "cand_cand_id" "comm_cand_id" "comm_cmte_nm")])
     ORDER-BY ()
     LIMIT (VAL 5)
    )


; Questions / missing ops
; 1. LIKEOP + NOT LIKEOP missing
; 2. How to denote COUNT(*): change to counting any non-null column (assuming no NaNs)
; 3. How to rename columns in select (e.g. SELECT col as colname): use AS on the outside
; 4. How to denote SELECT *: hardcode replace with all columns of table
; 5. ORDER-BY missing: test before ORDERING
; 6. LIMIT missing: test before LIMIT
; 7. Am I doing renaming using AS correctly? See q1d, q2b, q2c.
    ; When parsing student queries, override renaming of inner query. 
    ; This applies to all queries that are renamed