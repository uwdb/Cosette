#lang rosette

(require "../util.rkt" "../sql.rkt" "../table.rkt"  "../evaluator.rkt" "../equal.rkt")

;------ real tables (for debug) ------
(define RC (Table "Courses" (list "cid" "cname" "ch" "ppch")
                  (list
                   (cons (list 1 1 3 900) 1)
                   (cons (list 2 2 4 600) 1)
                   (cons (list 3 3 4 1100) 1)
                   (cons (list 4 4 4 1070) 1))))

(define RTB (Table "TB" (list "isbn")
                   (list
                    (cons (list 1) 1)
                    (cons (list 2) 1)
                    (cons (list 3) 1))))

(define RTBAssign (Table "TBAssign" (list "cid" "isbn")
                         (list
                          (cons (list 1 3) 1)
                          (cons (list 2 1) 1)
                          (cons (list 3 1) 1))))
  

;------ symbolic tables ------
(define Courses (Table "Courses" (list "cid" "cname" "ch" "ppch") (gen-sym-schema 4 2)))

(define TB (Table "TB" (list "isbn") (gen-sym-schema 1 2)))

(define TBAssign (Table "TBAssign" (list "cid" "isbn") (gen-sym-schema 2 2)))

;------ first query (WFEA) ------

; CREATE VIEW q1 AS [
; SELECT Courses.cid as cid, Courses.ch * Courses.ppch AS cost
; FROM Courses ]

(define q1
  (AS
   (SELECT
    (VALS "Courses.cid" (VAL-BINOP "Courses.ch" * "Courses.ppch"))
    FROM (NAMED Courses)
    WHERE (TRUE))
   ["q1" (list "cid" "cost")]))

; CREATE VIEW q2 [
; SELECT q1.cid, q1.cost
; FROM q1
; WHERE q1.cost > 2000 ]

(define q2
  (AS
   (SELECT
    (VALS "q1.cid" "q1.cost")
    FROM q1
    WHERE (BINOP "q1.cost" > 2000))
   ["q2" (list "cid" "cost")]))

; CREAT VIEW q3 [

; SELECT TB.isbn
; FROM TB INNER JOIN
;      ((q2 INNER JOIN Courses ON q2.cid=Courses.cid) INNER JOIN
;       TBAssign ON Courses.cid = TBAssign.cid)
;      ON TB.isbn = TBAssign.isbn
; GROUP BY TB.isbn

; which is equivalent to

; SELECT DISTINCT TB.isbn
; FROM TB, q2, Courses, TBAssign
; WHERE TB.isbn = TBAssign.isbn AND q2.cid = Courses.cid AND
;       Courses.cid = TBAssign.cid
; (currently our GROUP BY must be with aggregation,
; so I use select distinct.)

(define q3
  (AS
   (SELECT-DISTINCT
    (VALS "TB.isbn")
    FROM (JOIN
          (NAMED TB)
          (AS (JOIN
               (AS (JOIN q2 (NAMED Courses))
                   ["q2c" (list "q2_cid" "q2_cost" "c_cid" "c_cname" "c_ch" "c_ppch")])
               (NAMED TBAssign))
              ["q2ct" (list "q2_cid" "q2_cost" "c_cid" "c_cname" "c_ch" "c_ppch" "tba_cid" "tba_isbn")]))
    WHERE (AND (BINOP "TB.isbn" = "q2ct.tba_isbn")
               (AND (BINOP "q2ct.c_cid" = "q2ct.c_cid")
                    (BINOP "q2ct.c_cid" = "q2ct.tba_cid"))))
   ["q3" (list "isbn")]))


; CREATE VIEW wfea AS [
; SELECT COUNT(q3.isbn) as CountOfISBN
; FROM q3]

(define wfea
  (SELECT
   (VALS (AGGR aggr-count (SELECT (VALS "q3.isbn") FROM q3 WHERE (TRUE))))
   FROM (NAMED (UNIT))
   WHERE (TRUE)))


; ------ Second query (WFA) ------

; CREATE VIEW wfa

(define wfa
  (SELECT
   (VALS (AGGR aggr-count
               (SELECT (VALS "TB.isbn") FROM (NAMED TB) WHERE (TRUE))))
   FROM (NAMED (UNIT))
   WHERE (TRUE)))

(time (begin
        (assert-table-ordered TB)
        (assert-table-ordered TBAssign)
        (assert-table-ordered Courses)
        (verify (same wfea wfa))))

          
