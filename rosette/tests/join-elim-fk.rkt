#lang rosette 
 
(require "../cosette.rkt" "../util.rkt" "../table.rkt" 
         "../sql.rkt" "../evaluator.rkt" "../equal.rkt") 

 
(current-bitwidth #f)
 
(define t2-info (table-info "t2" (list "id" "t1_id" "n")))
 
(define t1-info (table-info "t1" (list "id" "n")))

(define t1 (Table "t1" (list "id" "n") (gen-sym-schema 2 2)))

(define t2 (Table "t2" (list "id" "t1_id" "n") (gen-sym-schema 3 2)))

(define q1 
  (SELECT (VALS "y.id" "y.n") 
  FROM (JOIN (NAMED (RENAME t1 "x")) (NAMED (RENAME t2 "y"))) 
  WHERE (BINOP "x.id" = "y.t1_id")))

(define q2 
  (SELECT (VALS "y.id" "y.n") 
  FROM (NAMED (RENAME t2 "y")) 
  WHERE (F-EMPTY)))

;(assert (foreign-key-constraint? t1 t2 (list 0) (list 1)))
;(assert (table-cols-distinct? t2 (list 2)))

(define (gen-t1-pk col)
  (assert (table-cols-distinct? t1 (list col))))

(define (gen-t2-pk col)
  (assert (table-cols-distinct? t2 (list col))))

(define (gen-fk col1 col2)
  (assert (foreign-key-constraint? t1 t2 (list col1) (list col2))))

(define t1pk 0)
(define t2pk 0)
(define t1-fk-pk 0)
(define t2-fk 0)

(define (stop-condition i j k n)
  (let ([sol
         (begin
           (gen-t1-pk i)
           (gen-t2-pk j)
           (gen-fk k n)
           (verify (same q1 q2)))])
    (cond
      [(sat? sol) #f]
      [else (begin (println "find")
                   (println (list i j k n))
                   (set! t1pk i)
                   (set! t2pk j)
                   (set! t1-fk-pk k)
                   (set! t2-fk n)
                   #t)])))
(time
(for* ([i (in-range 3)]
       [j (in-range 2)]
       [k (in-range 3)]
       [n (in-range 2)])
       #:break (stop-condition i j k n)
       (println (list i j k n))
 ))
;(verify (same q1 q2))
