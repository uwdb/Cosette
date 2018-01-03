#lang rosette

(require "../meta-solver.rkt" "../sql.rkt" 
         "../syntax.rkt" "../denotation.rkt" 
         "../table.rkt" "../evaluator.rkt" "../util.rkt")

(current-bitwidth #f)

(define c1 (c-conj (list (c-primitive (v-ref 0 2) > 0) (c-primitive (v-ref 0 4) = 3))))
;(println (to-str (meta-forall-eq 0 c1)))
;(println (to-str (meta-sum-eq 0 c1)))

(define cPicture
  (Table 
    "Picture" (list "uid" "size")
    (list
      (cons (list 3 100) 1)
      (cons (list 3 99) 1)
      (cons (list 8 150) 1))))

(define sPicture (Table "Picture" (list "uid" "size") (gen-sym-schema 2 1)))

(define Picture sPicture)

(define q1
  (SELECT 
    (VALS "Picture.size" "Picture.uid")
    FROM (NAMED Picture)
    WHERE (AND (BINOP "Picture.uid" = 3)
               (BINOP "Picture.size" = 100))))

;(println (to-str (init-constraint 5 1)))
;(assert (eq? (extract-sel-indices q1) '(1 0)))
(println (to-str-set (propogate q1 (list (init-constraint (length (extract-schema q1)) 1)) 1 999)))

(define q2
  (SELECT 
    (VALS "Picture.size")
    FROM (NAMED Picture)
    WHERE (AND (BINOP "Picture.uid" = 3)
               (AND (BINOP "Picture.size" > 98) (BINOP "Picture.size" < 101)))))

(println (to-str-set (propogate q2 (list (init-constraint (length (extract-schema q2)) 1)) 1 9999)))


(define q3
  (SELECT 
    (VALS "Picture.size")
    FROM (NAMED Picture)
    WHERE (AND (BINOP "Picture.uid" = 3)
               (AND (BINOP "Picture.size" > 99) (BINOP "Picture.size" < 101)))))

(println (to-str-set (propogate q3 (list (init-constraint (length (extract-schema q3)) 1)) 1 999)))


; (time (verify (same q1 q2)))
