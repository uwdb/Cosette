#lang rosette

(require "../cosette.rkt" "../util.rkt" "../table.rkt" 
         "../sql.rkt" "../evaluator.rkt" "../equal.rkt")

(define r (Table "r" (list "a") (gen-sym-schema 1 2)))

(define s (Table "s" (list "a1") (gen-sym-schema 1 1)))

(define-symbolic b (~> integer? boolean?))


; select * from r, (select * from s where b(s))

(define q1
  (SELECT
   (VALS "r.a" "s.a1")
   FROM (JOIN (NAMED r)
              (AS
               (SELECT
                (VALS "s.a1")
                FROM (NAMED s)
                WHERE (NARY-OP b "s.a1"))
               ["s" (list "a1")]))
   WHERE (F-EMPTY)))

; select * from r, s where b(s)

(define q2
  (SELECT
   (VALS "r.a" "s.a1")
   FROM (JOIN (NAMED r) (NAMED s))
   WHERE (NARY-OP b "s.a1")))


(verify (same q1 q2))
