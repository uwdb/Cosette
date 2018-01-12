#lang rosette

(require "../symmetry.rkt" "../sql.rkt" 
         "../syntax.rkt" "../denotation.rkt" 
         "../table.rkt" "../evaluator.rkt" "../util.rkt")

(current-bitwidth #f)

;(define c1 (c-conj (list (c-primitive (v-ref 0 2) > 0) (c-primitive (v-ref 0 4) = 3))))
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
    (VALS (VAL-BINOP "Picture.size" + 1)  "Picture.uid")
    FROM (NAMED Picture)
    WHERE (AND (BINOP "Picture.uid" = 3)
               (BINOP "Picture.size" = 100))))

(define q2
  (SELECT 
    (VALS "Picture.size")
    FROM (NAMED Picture)
    WHERE (AND (BINOP "Picture.uid" = 3)
               (AND (BINOP "Picture.size" > 98) (BINOP "Picture.size" < 101)))))

;(println (to-str-set (propogate q2 (list (init-constraint (length (extract-schema q2)) 1)) 1 9999)))

(define q3
  (SELECT 
    (VALS "Picture.size")
    FROM (NAMED Picture)
    WHERE (AND (BINOP "Picture.uid" = 3)
               (AND (BINOP "Picture.size" > 99) (BINOP "Picture.size" < 101)))))

;(displayln (to-str (small-step-sum-eq (init-constraint q1) 0)))
;(displayln (to-str (small-step-sum-eq (init-constraint q2) 0)))
;(displayln (to-str (small-step-sum-eq (init-constraint q3) 0)))
;(println (to-str-set (propogate q3 (list (init-constraint (length (extract-schema q3)) 1)) 1 999)))
(displayln (to-str (go-break-symmetry-bounded q1 q2)))
(displayln (to-str (go-break-symmetry-bounded q2 q3)))



; (time (verify (same q1 q2)))
