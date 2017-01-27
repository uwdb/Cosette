#lang rosette

(require "../util.rkt" "../sql.rkt" "../table.rkt"  "../evaluator.rkt" "../equal.rkt")

; ------- actual tables (only for test) -------

(define cUsr
  (Table "Usr" (list "uid" "uname" "city")
         (list
          (cons (list 3 4 1) 1)
          (cons (list 10 1 2) 1)
          (cons (list 9 1 3) 1)
          (cons (list 8 0 3) 1))))

(define cPicture
  (Table "Picture" (list "uid" "size")
         (list
          (cons (list 3 100) 1)
          (cons (list 10 200) 1)
          (cons (list 8 1500000) 1))))

(define cUsr2
  (Table "Usr" (list "uid" "uname" "city")
         (list
          (cons (list 0 0 3) 14)
          (cons (list 0 0 3) 5))))

(define cPicture2
  (Table "Picture" (list "uid" "size")
         (list
          (cons (list 0 0) 13)
          (cons (list 0 14) 13))))

; ------------ symbolic tables ----------------
; we need at least two rows

(define Usr (Table "Usr" (list "uid" "uname" "city") (gen-sym-schema 3 2)))

(define Picture (Table "Picture" (list "uid" "size") (gen-sym-schema 2 2)))

; ------------ verification ----------------------
; the example is taken from the final example of CSE 344
; https://courses.cs.washington.edu/courses/cse344/13au/exams/final-sol-13au.pdf

; Q1
; select x.uid, x.uname,
; (select count(*)
;      	from Picture y
; 	where x.uid = y.uid and y.size > 1000000)
; from Usr x
; where x.city = ’Denver’

(define q1
  (SELECT 
    (VALS "Usr.uid" "Usr.uname" 
          (AGGR aggr-count 
                (SELECT 
                  (VALS "Picture.uid" "Picture.size")
                  FROM (NAMED Picture)
                  WHERE (AND (BINOP "Usr.uid" = "Picture.uid")
                             (BINOP "Picture.size" > 1000000)))))
    FROM (NAMED Usr)
    WHERE (BINOP "Usr.city" = 3)))

; Q2
; select x.uid, x.uname, count(*)
; from Usr x, Picture y
; where x.uid = y.uid and y.size > 1000000 and x.city = ’Denver’
; group by x.uid, x.uname;

(define q2-part
  (AS 
    (SELECT 
    	(VALS "x.uid" "x.uname" "x.city" "y.uid" "y.size")
   	 FROM (JOIN (AS (NAMED Usr) ["x" (list "uid" "uname" "city")])
		       (AS (NAMED Picture) ["y" (list "uid" "size")]))
    	 WHERE (AND (AND (BINOP "x.uid" = "y.uid") (BINOP "y.size" > 1000000)) (BINOP "x.city" = 3)))
    ["table" (list "x_uid" "x_uname" "x_city" "y_uid" "y_size")]))

(define q2
  (SELECT-DISTINCT 
    (VALS "table.x_uid" "table.x_uname" 
	  (AGGR aggr-count 
		(SELECT 
		  (VALS "t.x_uid" "t.x_uname" "t.x_city" "t.y_uid" "t.y_size")
		  FROM (AS q2-part ["t" (list "x_uid" "x_uname" "x_city" "y_uid" "y_size")])
		  WHERE (AND (BINOP "t.x_uid" = "table.x_uid") (BINOP "t.x_uname" = "table.x_uname")))))
    FROM q2-part
    WHERE (F-EMPTY)))

; (run q1)
; (run q2-part)
;(extract-schema q2-part)

; (run q2)

; expect model

; Usr
; Picture

(time (verify (same q1 q2)))

