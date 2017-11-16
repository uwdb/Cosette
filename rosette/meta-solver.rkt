#lang rosette

(require  "sql.rkt" "syntax.rkt" "denotation.rkt" "table.rkt" "evaluator.rkt" "util.rkt")

(current-bitwidth #f)

(define (extract-sel-indices q)
  (let* ([schema (extract-schema (query-select-from-query q))]
         [name-hash (list->hash schema)]
         [args (query-select-select-args q)])
    (map (lambda (v) 
           (cond 
             [(val-column-ref? v) (hash-ref name-hash (val-column-ref-column-name v))]
             [else -1]))
         args)))

;; meta constraint lang

(struct meta-eq (qid constraint) #:transparent)
(struct meta-sum-eq (qid constraint) #:transparent)
(struct c-primitive (left op right) #:transparent)
(struct c-true ())
(struct c-false ())
(struct c-conj (preds) #:transparent)
(struct c-disj (preds) #:transparent)
(struct r-ref (idx) #:transparent)

;; given a constraint 
(define (to-str v)
  (cond
    [(meta-eq? v) (format "\u2200r. ~a \u21D2 \u27E6~a(T)\u27E7r = \u27E6~a(T')\u27E7r" 
                          (to-str (meta-eq-constraint v)) (meta-eq-qid v) (meta-eq-qid v))]
    [(meta-sum-eq? v) (format "\u2211 { \u27E6~a(T)\u27E7 r | ~a } =  \u2211 { \u27E6~a(T')\u27E7 r | ~a }" 
                          (meta-sum-eq-qid v) (to-str (meta-sum-eq-constraint v)) (meta-sum-eq-qid v) (to-str (meta-sum-eq-constraint v)))]
    [(r-ref? v) (format "r[~a]" (r-ref-idx v))]     
    [(c-primitive? v) 
     (format "~a ~a ~a" (to-str (c-primitive-left v)) (c-primitive-op v) (to-str (c-primitive-right v)))]
    [(c-true? v) "#t"]
    [(c-false? v) "#f"]
    [(c-conj? v) 
     (let ([content (map (lambda (x) (format "(~a)" (to-str x))) (c-conj-preds v))])
      (format "~a" (foldl (lambda (x y) (format "~a \u2227 ~a" x y)) (car content) (cdr content))))]
    [(c-disj? v) (let ([content (map (lambda (x) (to-str x)) (c-conj-preds v))])
      (format "~a" (foldl (lambda (x y) (format "~a \u2228 ~a" x y)) (car content) (cdr content))))]
    [else v]))

;;; test

(define c1 (c-conj (list (c-primitive (r-ref 2) > 0) (c-primitive (r-ref 4) = 3))))
(println (to-str (meta-eq "q1" c1)))
(println (to-str (meta-sum-eq "q1" c1)))

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
    (VALS "Picture.size")
    FROM (NAMED Picture)
    WHERE (AND (BINOP "Picture.uid" = 3)
               (BINOP "Picture.size" = 100))))

(define q2
  (SELECT 
    (VALS "Picture.size")
    FROM (NAMED Picture)
    WHERE (AND (BINOP "Picture.uid" = 3)
               (AND (BINOP "Picture.size" > 98) (BINOP "Picture.size" < 101)))))

(define q3
  (SELECT 
    (VALS "Picture.size")
    FROM (NAMED Picture)
    WHERE (AND (BINOP "Picture.uid" = 3)
               (AND (BINOP "Picture.size" > 99) (BINOP "Picture.size" < 101)))))

(time (verify (same q1 q2)))

;(define (csym-eq-update constraint)
;	(let ([q (csym-eq-query constraint)]
;			  [r (csym-eq-row constraint)]
;			  [m (csym-eq-row constraint)])
;		(cond 
;			[(query-select? q) 
;				(let ([select-indices ]))])
;	))
;
;
;(define (symmetry-analysis constraint)
;	(cond 
;		[(csym-eq? constraint)
;		 (let [q (csym-eq-query constraint)]
;			(cond 
;				[()]))]
;	))
;
;(define (symmetry-analysis csym-list)
;	)
