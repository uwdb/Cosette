;; psg-bug: https://www.postgresql.org/message-id/flat/201009231503.o8NF3Blt059661%40wwwmaster.postgresql.org#201009231503.o8NF3Blt059661@wwwmaster.postgresql.org

;; the original query
;SELECT * 
;FROM   "defaultpropertyvalues" AS "Extent1" 
;       INNER JOIN "defaultpropertyvalues" AS "Extent2" 
;               ON "Extent1.id" = "Extent2.id" 
;       LEFT JOIN (SELECT "UnionAll1.id" AS "C1", 
;                         "UnionAll1.c1" AS "C2", 
;                         "UnionAll1.c2" AS "C3", 
;                         "UnionAll1.c3" AS "C4", 
;                         "UnionAll1.c4" AS "fk_EnumVal" 
;                  FROM   (SELECT "Extent3"."id"      AS "ID", 
;                                 true                AS "C1", 
;                                 false               AS "C2", 
;                                 false               AS "C3", 
;                                 Cast (NULL AS INT4) AS "C4" 
;                          FROM   "currentdatetimedefaultvalues" AS 
;                                 "Extent3" 
;                          UNION ALL 
;                          SELECT "Extent4.id"      AS "ID", 
;                                 true                AS "C1", 
;                                 false               AS "C2", 
;                                 true                AS "C3", 
;                                 Cast (NULL AS INT4) AS "C4" 
;                          FROM   "newguiddefaultvalues" AS "Extent4") AS 
;                         "UnionAll1" 
;                  UNION ALL 
;                  SELECT "Extent5.id"           AS "ID", 
;                         false                    AS "C1", 
;                         true                     AS "C2", 
;                         false                    AS "C3", 
;                         "Extent5.fk_enumvalue" AS "fk_EnumValue" 
;                  FROM   "enumdefaultvalues" AS "Extent5") AS "UnionAll2" 
;              ON "Extent2.id" = "UnionAll2.c1" 
;WHERE  ( "Extent1.fk_property" IS NOT NULL ) AND ( "Extent1.fk_property" = 783 ) 

#lang rosette                                                                                                                                                 
(require "../util.rkt" "../symmetry.rkt" "../sql.rkt" "../table.rkt"  "../evaluator.rkt" "../equal.rkt")

;=============================== Concrete tables for testing =====================

(define ct1
    (Table "DefaultPropertyValues" (list "ID" "fk_Property")
	   (list (cons (list 0 0) 1))))

(define ct4
  (Table "CurrentDateTimeDefaultValues" (list "ID" "C")
	 (list (cons (list 3 4) 1))))

(define ct5
  (Table "EnumDefaultValues" (list "ID" "C")
	 (list (cons (list 0 0) 7))))

;=========================== Symbolic tables for verification =============

(current-bitwidth 32)
(define st1 (Table "DefaultPropertyValues" (list "ID" "fk_Property") (gen-sym-schema 2 1)))
(define st4 (Table "CurrentDateTimeDefaultValues" (list "ID" "C") (gen-sym-schema 2 1)))
(define st5 (Table "EnumDefaultValues" (list "ID" "C") (gen-sym-schema 2 1)))

; ========================= Define tables ====================================

(define t1 st1)
(define t4 st4)
(define t5 st5)

;01 Nested Loop Left Join  
;02   Join Filter: ("Extent2"."ID" = "Extent3"."ID")"
;03   ->  Hash Join
;04         Hash Cond: ("Extent2"."ID" = "Extent1"."ID")"
;05         ->  Seq Scan on "DefaultPropertyValues" "Extent2" 
;06         ->  Hash  
;07               ->  Seq Scan on "DefaultPropertyValues" "Extent1" 
;08                     Filter: (("fk_Property" IS NOT NULL) AND ("fk_Property" = 783))"
;09   ->  Append  
;10         ->  Append  
;11               ->  Seq Scan on "CurrentDateTimeDefaultValues" "Extent3" 
;12               ->  Seq Scan on "NewGuidDefaultValues" "Extent4" 
;13               ->  Seq Scan on "EnumDefaultValues" "Extent5" 
;14         ->  Index Scan using "PK_[zbox].[dbo].[EnumDefaultValues]" on "EnumDefaultValues" "Extent5"  
;15               Index Cond: ("Extent2"."ID" = "Extent5"."ID")"


; q0 is the original query
(define q0-part-1
  (AS
    (SELECT (VALS "t12.ID1" "t12.fk_Property1" "t12.ID2" "t12.fk_Property2")
      FROM (AS (JOIN (AS (NAMED t1) ["t1" (list "ID" "fk_Property")])
		     (AS (NAMED t1) ["t2" (list "ID" "fk_Property")]))
	       ["t12" (list "ID1" "fk_Property1" "ID2" "fk_Property2")])
     WHERE (BINOP "t12.ID1" = "t12.ID2"))
    ["t12" (list "ID1" "fk_Property1" "ID2" "fk_Property2")]))

(define q0-part-2
  (AS 
    (UNION-ALL 
      (NAMED t4)
      (NAMED t5))
    ["UnionAll2" (list "ID" "C")]))

(define q0-part-3
  (AS (LEFT-OUTER-JOIN q0-part-1 q0-part-2 0 0)
      ["J1" (list "ID1" "fk_Property1" "ID2" "fk_Property2" "ID3" "C")]))

(define q0
  (SELECT 
    (VALS "J1.ID1" "J1.fk_Property1" "J1.ID2" "J1.fk_Property2" "J1.ID3" "J1.C")
    FROM q0-part-3
    WHERE (AND (BINOP "J1.fk_Property1" (lambda (x y) (not (equal? x y))) sqlnull)
	       (BINOP "J1.fk_Property1" = 783))))

; lines 05-08
(define q1-part-1
  (AS
    (SELECT 
      (VALS "t1.ID" "t1.fk_Property")
      FROM (AS (NAMED t1) ["t1" (list "ID" "fk_Property")])
      WHERE (AND (BINOP "t1.fk_Property" (lambda (x y) (not (equal? x y))) sqlnull)
		 (BINOP "t1.fk_Property" = 783)))
    ["t1" (list "ID" "fk_Property")]))

; lines 01-08
(define q1-part-2
  (SELECT 
    (VALS "t12.ID1" "t12.fk_Property1" "t12.ID2" "t12.fk_Property2")
    FROM (AS 
	   (JOIN (NAMED t1)
		 q1-part-1)
	   ["t12" (list "ID1" "fk_Property1" "ID2" "fk_Property2")])
    WHERE (BINOP "t12.ID1" = "t12.ID2")))

; lines 14-15
(define q1-part-3
   (SELECT
     (VALS "t5.ID" "t5.C")
     FROM (AS (NAMED t5) ["t5" (list "ID" "C")])
     WHERE (EXISTS 
	     (SELECT (VALS "t2.ID")
	      FROM (AS (NAMED t1) ["t2" (list "ID" "fk_Property")])
	      WHERE (BINOP "t5.ID" = "t2.ID")))))

(define q1-part-4
  (AS 
    (UNION-ALL  
      (UNION-ALL (NAMED t4) 
		 (NAMED t5))
      q1-part-3) ["U" (list "ID" "C")]))

(define q1
  (AS (LEFT-OUTER-JOIN q1-part-2 q1-part-4 0 0)
      ["R" (list "ID1" "fk_Property1" "ID2" "fk_Property2" "ID3" "C")]))

(define q2-part-2 q1-part-2)
(define q2-part-4
  (AS (UNION-ALL (NAMED t4) 
		 (NAMED t5))
      ["U" (list "ID" "C1")]))

(define q2
    (AS (LEFT-OUTER-JOIN q2-part-2 q2-part-4 0 0)     
	["R" (list "ID1" "fk_Property1" "ID2" "fk_Property2" "ID3" "C1")]))

;(run q0)
;(run q1-part-4)
;(run q2)

(go-break-symmetry-bounded q0 q2)

;(verify (same q0-part-2 q2-part-4))
;(verify (same q0 q1))
(verify (same q0 q2))

;EXPLAIN ANALYZE:
;01 Nested Loop Left Join
;02   Join Filter: ("Extent2"."ID" = "Extent3"."ID")"
;03   ->  Hash Join 
;04         Hash Cond: ("Extent2"."ID" = "Extent1"."ID")"
;05         ->  Seq Scan on "DefaultPropertyValues" "Extent2" 
;06         ->  Hash 
;07               ->  Seq Scan on "DefaultPropertyValues" "Extent1" 
;08                     Filter: (("fk_Property" IS NOT NULL) AND ("fk_Property" = 783))"
;09   ->  Append
;10         ->  Seq Scan on "CurrentDateTimeDefaultValues" "Extent3" 
;11         ->  Seq Scan on "NewGuidDefaultValues" "Extent4" 
;12         ->  Seq Scan on "EnumDefaultValues" "Extent5"


