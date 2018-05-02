#lang rosette 
 
(require "../cosette.rkt" "../util.rkt" "../denotation.rkt" "../cosette.rkt" "../sql.rkt" "../evaluator.rkt" "../syntax.rkt" "../symmetry.rkt" "../test-util.rkt") 
  
(provide ros-instance)  

(current-bitwidth #f)

(define t0 (table-info "input" (list "user_id" "account_no" "zip" "date")))
 
(define (q5 tables) 
(SELECT (VALS "t2.user_id" "t2.count_date" )
 FROM (AS (SELECT (VALS "t1.user_id" "t1.account_no" "t1.zip" (VAL-UNOP aggr-count (val-column-ref "t1.date")) )
 FROM (AS (NAMED (list-ref tables 0)) ["t1" (list "user_id" "account_no" "zip" "date")])
 WHERE (TRUE)
 GROUP-BY (list "t1.user_id" "t1.account_no" "t1.zip" )
 HAVING (TRUE)) ["t2" (list "user_id" "account_no" "zip" "count_date")])
 WHERE (AND (BINOP "t2.count_date" > "t2.user_id") (TRUE))))
 
(define (q4 tables) 
(SELECT (VALS "t1.user_id" "t1.count_zip" )
 FROM (AS (SELECT (VALS "t2.user_id" "t2.account_no" "t2.zip" (VAL-UNOP aggr-count (val-column-ref "t2.zip")) )
 FROM (AS (NAMED (list-ref tables 0)) ["t2" (list "user_id" "account_no" "zip" "date")])
 WHERE (TRUE)
 GROUP-BY (list "t2.user_id" "t2.account_no" "t2.zip" )
 HAVING (TRUE)) ["t1" (list "user_id" "account_no" "zip" "count_zip")])
 WHERE (AND (BINOP "t1.count_zip" > "t1.user_id") (TRUE))))
 
(define (q3 tables) 
(SELECT (VALS "t1.user_id" "t1.count_account_no" )
 FROM (AS (SELECT (VALS "t2.user_id" "t2.account_no" "t2.date" (VAL-UNOP aggr-count (val-column-ref "t2.account_no")) )
 FROM (AS (NAMED (list-ref tables 0)) ["t2" (list "user_id" "account_no" "zip" "date")])
 WHERE (TRUE)
 GROUP-BY (list "t2.user_id" "t2.account_no" "t2.date" )
 HAVING (TRUE)) ["t1" (list "user_id" "account_no" "date" "count_account_no")])
 WHERE (AND (BINOP "t1.count_account_no" > "t1.user_id") (TRUE))))
 
(define (q2 tables) 
(SELECT (VALS "t1.user_id" "t1.count_date" )
 FROM (AS (SELECT (VALS "t2.user_id" "t2.account_no" "t2.date" (VAL-UNOP aggr-count (val-column-ref "t2.date")) )
 FROM (AS (NAMED (list-ref tables 0)) ["t2" (list "user_id" "account_no" "zip" "date")])
 WHERE (TRUE)
 GROUP-BY (list "t2.user_id" "t2.account_no" "t2.date" )
 HAVING (TRUE)) ["t1" (list "user_id" "account_no" "date" "count_date")])
 WHERE (AND (BINOP "t1.count_date" > "t1.user_id") (TRUE))))
 
(define (q1 tables) 
(SELECT (VALS "t2.user_id" "t2.count_account_no" )
 FROM (AS (SELECT (VALS "t1.user_id" "t1.account_no" "t1.zip" (VAL-UNOP aggr-count (val-column-ref "t1.account_no")) )
 FROM (AS (NAMED (list-ref tables 0)) ["t1" (list "user_id" "account_no" "zip" "date")])
 WHERE (TRUE)
 GROUP-BY (list "t1.user_id" "t1.account_no" "t1.zip" )
 HAVING (TRUE)) ["t2" (list "user_id" "account_no" "zip" "count_account_no")])
 WHERE (AND (BINOP "t2.count_account_no" > "t2.user_id") (TRUE))))

(define ros-instance (list q1 q2 (list t0)))
