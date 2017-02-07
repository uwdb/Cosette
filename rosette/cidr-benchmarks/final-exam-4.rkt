#lang rosette

(require "../util.rkt" "../sql.rkt" "../table.rkt"  "../evaluator.rkt" "../equal.rkt")

; ------- actual tables (only for test) -------

(define cUsr
  (Table "Usr" (list "uid" "uname")
         (list
          (cons (list 3 4) 1)
          (cons (list 10 1) 1)
          (cons (list 9 1) 1)
          (cons (list 8 0) 1))))

(define cPicture
  (Table "Picture" (list "uid" "size")
         (list
          (cons (list 3 100) 1)
          (cons (list 10 200) 1)
          (cons (list 8 1500000) 1))))

(define cUsr2
  (Table "Usr" (list "uid" "uname")
         (list
          (cons (list 10 0) 1))))

(define cPicture2
  (Table "Picture" (list "uid" "size")
         (list
          (cons (list 10 4) 2)
          (cons (list 10 0) 9))))

; ------------ symbolic tables ----------------
; we need at least two rows

; overwrite rosette's default bitwidth
(current-bitwidth 32)

(define sUsr (Table "Usr" (list "uid" "uname") (gen-sym-schema 2 1)))

(define sPicture (Table "Picture" (list "uid" "size") (gen-sym-schema 2 2)))

; ------------- define tables input to the system ---------------

(define Usr sUsr)
(define Picture sPicture)
(define a 1000000)
(define b 3000000)

; (define a 1)
; (define b 16)


; ------------ verification ----------------------
; the example is taken from the final example of CSE 344
; https://courses.cs.washington.edu/courses/cse344/13au/exams/final-sol-13au.pdf

; Q1
; select distinct x.uid, x.uname
; from Usr x, Picture u, Picture v, Picture w
; where x.uid = u.uid and x.uid = v.uid and x.uid = w.uid
; and u.size > 1000000 and v.size < 3000000 and w.size = u.size;

(define q1
  (SELECT-DISTINCT 
    (VALS "t.x_uid" "t.x_uname")
    FROM (AS 
	   (JOIN (NAMED Usr)
		 (JOIN (NAMED Picture)
		       (JOIN (NAMED Picture) (NAMED Picture))))
	   ["t" (list "x_uid" "x_uname" "u_uid" "u_size" "v_uid" "v_size" "w_uid" "w_size")])
    WHERE (AND (BINOP "t.x_uid" = "t.u_uid")
               (AND (BINOP "t.x_uid" = "t.v_uid")
                    (AND (BINOP "t.x_uid" = "t.w_uid")
                         (AND (BINOP "t.u_size" > a)
                              (AND (BINOP "t.v_size" < b)
                                   (BINOP "t.w_size" = "t.u_size"))))))))

; (run q1-part)

; Q2
; select distinct x.uid, x.uname
; from Usr x, Picture u, Picture w
; where x.uid = u.uid and x.uid = w.uid
; and u.size > 1000000 and u.size < 3000000 and u.size = w.size;

(define q2
  (SELECT-DISTINCT 
    (VALS "t.x_uid" "t.x_uname")
    FROM (AS 
	   (JOIN (NAMED Usr)
		 (JOIN (NAMED Picture) (NAMED Picture)))
	   ["t" (list "x_uid" "x_uname" "u_uid" "u_size" "w_uid" "w_size")])
    WHERE (AND (BINOP "t.x_uid" = "t.u_uid")
               (AND (BINOP "t.x_uid" = "t.w_uid")
                    (AND (BINOP "t.u_size" > a)
                         (AND (BINOP "t.u_size" < b)
                              (BINOP "t.w_size" = "t.u_size")))))))

; (run q1)
; (run q2-part)
; (extract-schema q2-part)
; (run q2)

; expect model

; Usr
; Picture

;(run q1)
;(run q2)
;(bag-equal (get-content (run q1))  (get-content (run q2)))

(time (verify (same q1 q2)))

