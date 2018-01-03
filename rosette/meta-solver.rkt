#lang rosette

(require "sql.rkt" "syntax.rkt" "denotation.rkt" "table.rkt" "evaluator.rkt" "util.rkt")

(provide (all-defined-out))

(define (extract-sel-indices q)
  (let* ([schema (extract-schema (query-select-from-query q))]
         [name-hash (list->hash schema)]
         [args (query-select-select-args q)])
    (map (lambda (v) 
           (cond 
             [(val-column-ref? v) (hash-ref name-hash (val-column-ref-column-name v))]
             [else -1]))
         args)))

;; meta constraint language

(struct meta-forall-eq (constraint) #:transparent)
(struct meta-sum-eq (constraint) #:transparent)

; c-primitive is a constraint that converts values comparison result into a boolean
(struct c-primitive (left op right) #:transparent)
(struct c-true ())
(struct c-false ())
(struct c-conj (preds) #:transparent)
(struct c-disj (preds) #:transparent)
(struct c-neg (pred) #:transparent)

(struct v-const (c) #:transparent)
(struct v-bexpr (op v1 v2) #:transparent)
(struct v-uexpr (op v) #:transparent)
(struct v-ref (qid cid) #:transparent) ; referencing a cell in the row
(struct v-symval (id) #:transparent)

;; given a constraint, print it as a string for the purpose of reading
(define (to-str v)
  (cond
    [(meta-forall-eq? v) (format "\u2200{ ~a }" (to-str (meta-forall-eq-constraint v)))]
    [(meta-sum-eq? v) (format "\u2211{ ~a }" (to-str (meta-sum-eq-constraint v)))]
    [(c-primitive? v) 
     (format "~a ~a ~a" (to-str (c-primitive-left v)) (c-primitive-op v) (to-str (c-primitive-right v)))]
    [(c-true? v) "T"]
    [(c-false? v) "F"]
    [(c-conj? v) 
     (let ([content (map (lambda (x) (format "(~a)" (to-str x))) (c-conj-preds v))])
       (format "~a" (foldl (lambda (x y) (format "~a \u2227 ~a" x y)) (car content) (cdr content))))]
    [(c-disj? v) 
      (let ([content (map (lambda (x) (to-str x)) (c-conj-preds v))])
        (format "~a" (foldl (lambda (x y) (format "~a \u2228 ~a" x y)) (car content) (cdr content))))]
    [(c-neg? v) (format "\u00AC ~a" (to-str (c-neg-pred v)))]
    [(v-const? v) (format "~a" (v-const-c v))]
    [(v-uexpr? v) (format "~a ~a" (v-uexpr-op v) (v-uexpr-v v))]
    [(v-bexpr? v) (format "~a ~a ~a" (v-bexpr-v1 v) (v-bexpr-op v) (v-bexpr-v2 v))]
    [(v-ref? v) (format "r~a[~a]" (v-ref-qid v) (v-ref-cid v))]
    [(v-symval? v) (format "@~a" (v-symval-id v))]
    [else v]))

(define (to-str-set v-set)
  (foldl (lambda (v r) (string-append r (to-str v) "  ")) ""  v-set))

(define (init-constraint tuple-size qid)
  (meta-forall-eq (c-conj (build-list tuple-size (lambda (x) (c-primitive (v-ref qid x) = (v-symval x)))))))


; convert sql val expr into meta v expr
(define (v-from-sql-val v vmap qid) 
  ; generate a meta constraint v expr from a vmap
  ; vmap maps each column-ref primitive into a v-ref that uses the row id
  (cond 
    [(val-const? v) (v-const (val-const-val v))]
    [(val-column-ref? v) (v-ref qid (hash-ref vmap (val-column-ref-column-name v)))]
    [(val-uexpr? v) (v-uexpr (val-uexpr-op v) (v-from-sql-val (val-uexpr-val v) vmap qid))]
    [(val-bexpr? v) (v-bexpr (val-bexpr-binop v) 
                             (v-from-sql-val (val-bexpr-v1 v) vmap qid) 
                             (v-from-sql-val (val-bexpr-v2 v) vmap qid))]))


(define (c-from-sql-filter f vmap qid)
  ; generate a meta constraint v expr from a vmap
  ; vmap maps each column-ref primitive into a v-ref that uses the row id
  (cond 
    [(filter-binop? f) (c-primitive (v-from-sql-val (filter-binop-val1 f) vmap qid)
                                    (filter-binop-op f) 
                                    (v-from-sql-val (filter-binop-val2 f) vmap qid))]
    [(filter-conj? f) (c-conj (list (c-from-sql-filter (filter-conj-f1 f) vmap qid)
                                    (c-from-sql-filter (filter-conj-f2 f) vmap qid)))]
    [(filter-disj? f) (c-disj (list (c-from-sql-filter (filter-disj-f1 f) vmap qid)
                                    (c-from-sql-filter (filter-disj-f2 f) vmap qid)))]
    [(filter-not? f) (c-neg (c-from-sql-filter (filter-not-f1 f) vmap qid))]
    [(filter-true? f) (c-true)]
    [(filter-false? f) (c-false)]
    ; currently not supporting n-nary filter operation
    ))


(define (subst-v-ref v ref-map qid)
  ; subst values in the constriant based on ref-map, 
  ; only v-ref whose v-ref-qid matches the qid would be substituted
  (cond
    [(meta-forall-eq? v) (meta-forall-eq (subst-v-ref (meta-forall-eq-constraint v) ref-map qid))]
    [(meta-sum-eq? v) (meta-sum-eq (subst-v-ref (meta-sum-eq-constraint v) ref-map qid))]
    [(c-primitive? v)
     (c-primitive (subst-v-ref (c-primitive-left v) ref-map qid) 
                  (c-primitive-op v) 
                  (subst-v-ref (c-primitive-right v) ref-map qid))]
    [(c-true? v) v]
    [(c-false? v) v]
    [(c-conj? v) (c-conj (map (lambda (x) (subst-v-ref x ref-map qid)) (c-conj-preds v)))]
    [(c-disj? v) (c-disj (map (lambda (x) (subst-v-ref x ref-map qid)) (c-disj-preds v)))]
    [(c-neg? v) (c-neg (subst-v-ref (c-neg-pred v) ref-map qid))]
    [(v-const? v) v]
    [(v-uexpr? v) (v-uexpr (v-uexpr-op v) (subst-v-ref (v-uexpr-v v) ref-map qid))]
    [(v-bexpr? v) (v-bexpr (subst-v-ref (v-bexpr-v1 v) ref-map qid) 
                           (v-bexpr-op v) 
                           (subst-v-ref (v-bexpr-v2 v) ref-map qid))]
    [(v-ref? v)
     (cond 
       [(eq? (v-ref-qid v) qid) (list-ref ref-map (v-ref-cid v))]
       [else v])]
    [(v-symval? v) v]
    [else v]))


(define (extend-conj c pred)
  (cond 
    [(meta-forall-eq? c) 
     (meta-forall-eq (c-conj (list (meta-forall-eq-constraint c) pred)))]
    [(meta-sum-eq? c) 
     (meta-sum-eq (c-conj (list (meta-sum-eq-constraint c) pred)))]))


; given a set of constraints, propogate the constraint to the finest level 
(define (propogate query constraints qid step)
  (cond 
    [(eq? step 0) constraints]
    [(query-named? query)
     (let ([ref-map (map (lambda (i) (v-ref (string-append (Table-name (query-named-table-ref query)) 
                                                           (number->string qid)) i)) 
                         (build-list (length (Table-schema (query-named-table-ref query))) values))])
       (map (lambda (c) (subst-v-ref c ref-map qid)) constraints))]
    [(query-select? query)
     (let* ([inner-q (query-select-from-query query)]
            [sel-args (query-select-select-args query)]
            [sel-pred (query-select-where-filter query)]
            [inner-q-schema (extract-schema inner-q)]
            [inner-q-name-hash (list->hash inner-q-schema)]
            [new-qid (* qid 2)]
            [ref-map (map (lambda (v) (v-from-sql-val v inner-q-name-hash new-qid)) sel-args)])
       (propogate
         inner-q 
         (map (lambda (c) (extend-conj (subst-v-ref c ref-map qid)
                                       (c-from-sql-filter sel-pred inner-q-name-hash new-qid))) 
              constraints)
         new-qid (- step 1))
       )]
    [(query-join? query)
     (let* ([q1 (query-join-query1 query)]
            [q2 (query-join-query2 query)]
            [q1-schema (extract-schema q1)]
            [q2-schema (extract-schema q2)]
            [q1-name-hash (list->hash q1-schema)]
            [q2-name-hash (list->hash q2-schema)]
            [q1-new-qid (* qid 2)]
            [q2-new-qid (+ (* qid 2) 1)]
            [ref-map 
             (map (lambda (i) (cond [(< i (length q1-schema)) (v-ref q1-new-qid i)] 
                                    [else (v-ref q2-new-qid (- i (length q1-schema)))]))
                  (build-list (+ (length q1-schema) (length q2-schema)) values))]
            [constraints1 (map (lambda (c) (subst-v-ref c ref-map qid)) constraints)]
            [constraints2 (propogate q1 constraints1 q1-new-qid (- step 1))])
       (propogate q2 constraints2 q2-new-qid (- step 1)))]
    [(or (query-rename-full? query) (query-rename? query))
     (let* ([q (cond [(query-rename-full? query) (query-rename-full-query query)]
                     [(query-rename? query) (query-rename-query query)])]
            [new-qid (* qid 2)]
            [ref-map (map (lambda (i) (v-ref new-qid i))
                          (build-list (length (extract-schema query)) values))]
            [updated-constraints (map (lambda (c) (subst-v-ref c ref-map qid)) constraints)])
       (propogate q updated-constraints new-qid (- step 1)))]
    ;[(query-union-all? query)]
    [else constraints]))

;;; test

