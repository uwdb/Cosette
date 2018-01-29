#lang rosette

(require "syntax.rkt" "denotation.rkt" "evaluator.rkt" "table.rkt")

(provide (all-defined-out))

;; meta constraint language
(struct forall-eq (query constr) #:transparent)
(struct sum-eq (queries constr) #:transparent)

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
(struct v-ref (id) #:transparent) ; referencing a cell in the row
(struct v-symval (id) #:transparent) ; a symbolic value with its id

;;;;;;;;;;;; functions for generating symmetry breaking conditions ;;;;;;;;;;;;

(define (go-break-symmetry-bounded q1 q2)
  (let* ([c1 (big-step (init-forall-eq-constraint q1) 20)]
         [c2 (big-step (init-forall-eq-constraint q2) 20)]
         [flat-constr (flatten (list c1 c2))])
   (merge-forall-eq flat-constr)))

(define (go-break-symmetry-bounded-intersect q1 q2)
  ; perform an intersection to reduce 
  (let* ([c1 (big-step (init-forall-eq-constraint q1) 20)]
         [c2 (big-step (init-forall-eq-constraint q2) 20)]
         [flat-constr (flatten (list c1 c2))])
   (merge-forall-eq-intersect flat-constr)))

(define (init-constraint query)
  ; initialize a the constraint for symmetry breaking
  (sum-eq (list query) 
          (c-conj (build-list (length (extract-schema query)) 
                              (lambda (x) (c-primitive (v-ref x) = (v-symval x)))))))

(define (init-forall-eq-constraint query)
  ; initialize a the constraint for symmetry breaking
  (forall-eq query
             (c-conj (build-list (length (extract-schema query)) 
                                 (lambda (x) (c-primitive (v-ref x) = (v-symval x)))))))

(define (big-step mconstr fuel)
  ; big-step semantics for constraint propogation,
  ; fuel is supposed to be greater or equal than depth of the ast
  (cond
    [(eq? fuel 0) mconstr]
    [(forall-eq? mconstr) (big-step (small-step-forall-eq mconstr) (- fuel 1))]
    [(sum-eq? mconstr) (big-step (small-step-sum-eq mconstr 0) (- fuel 1))]
    [(list? mconstr) (map (lambda (mc) (big-step mc fuel)) mconstr)]))

(define (sum-eq->forall-eq mconstr)
  ; generates forall-eq to sum-eq, 
  ; which strenghtens the constraint (as the space is further restricted)
  (let ([queries (sum-eq-queries mconstr)]
        [core (sum-eq-constr mconstr)])
    (if (eq? (length queries) 1)
      (forall-eq (car queries) core)
      (forall-eq (foldl (lambda (v r) (query-join r v)) (car queries) (cdr queries)) core))))

(define (small-step-sum-eq mconstr index)
  ; small step semantics for propogating sum-eq constraints 
  (cond 
    [(>= index (length (sum-eq-queries mconstr))) mconstr] ; no need to update query
    [else
      (let* ([queries (sum-eq-queries mconstr)]
             [query (list-ref queries index)]
             [queries-before (take queries index)]
             [queries-after (drop queries (+ index 1))]
             [q-schema-size (length (extract-schema query))]
             [schema-size-before 
              (foldl + 0 (map (lambda (q) (length (extract-schema q))) queries-before))]
             [schema-size-after 
              (foldl + 0 (map (lambda (q) (length (extract-schema q))) queries-after))])
        (cond
          [(query-named? (list-ref queries index)) ; no step needed, move to the next index
           (small-step-sum-eq mconstr (+ index 1))]
          [(query-select-distinct? query)
           (let* ([inner-q (query-select-distinct-from-query query)]
                  [sel-args (query-select-distinct-select-args query)]
                  [sel-pred (query-select-distinct-where-filter query)]
                  [inner-q-schema (extract-schema inner-q)]
                  [inner-q-schema-size (length (extract-schema inner-q))]
                  [inner-q-name-hash 
                    (make-hash (map (lambda (i) (cons (list-ref inner-q-schema i) 
                                                      (+ i schema-size-before))) 
                                    (build-list (length inner-q-schema) values)))]
                  [ref-map
                    (append 
                      (build-list schema-size-before values)
                      (map (lambda (v) (v-from-sql-val v inner-q-name-hash)) sel-args)
                      (build-list schema-size-after 
                                  (lambda (x) (+ x schema-size-before inner-q-schema-size))))])
             (sum-eq
               (append queries-before (list inner-q) queries-after)
               (c-conj (list (subst-v-ref (sum-eq-constr mconstr) ref-map) 
                             (c-from-sql-filter sel-pred inner-q-name-hash)))))]
          [(query-select? query)
           (let* ([inner-q (query-select-from-query query)]
                  [sel-args (query-select-select-args query)]
                  [sel-pred (query-select-where-filter query)]
                  [inner-q-schema (extract-schema inner-q)]
                  [inner-q-schema-size (length (extract-schema inner-q))]
                  [inner-q-name-hash 
                    (make-hash (map (lambda (i) (cons (list-ref inner-q-schema i) 
                                                      (+ i schema-size-before))) 
                                    (build-list (length inner-q-schema) values)))]
                  [ref-map
                    (append 
                      (build-list schema-size-before values)
                      (map (lambda (v) (v-from-sql-val v inner-q-name-hash)) sel-args)
                      (build-list schema-size-after 
                                  (lambda (x) (+ x schema-size-before inner-q-schema-size))))])
             (sum-eq
               (append queries-before (list inner-q) queries-after)
               (c-conj (list (subst-v-ref (sum-eq-constr mconstr) ref-map) 
                             (c-from-sql-filter sel-pred inner-q-name-hash)))))]
          [(query-join? query)
           (let* ([q1 (query-join-query1 query)]
                  [q2 (query-join-query2 query)])
             (sum-eq (append queries-before (list q1 q2) queries-after)
                     (sum-eq-constr mconstr)))]
          [(or (query-rename-full? query) (query-rename? query))
           (let* ([q (cond [(query-rename-full? query) (query-rename-full-query query)]
                           [(query-rename? query) (query-rename-query query)])])
             (sum-eq (append queries-before (list q) queries-after)
                     (sum-eq-constr mconstr)))]
          [(query-union-all? query)
           (let* ([q1 (query-union-all-query1 query)]
                  [q2 (query-union-all-query2 query)])
             (list
               (sum-eq (append queries-before (list q1) queries-after)
                       (sum-eq-constr mconstr))
               (sum-eq (append queries-before (list q2) queries-after)
                       (sum-eq-constr mconstr))))]
          [else (small-step-forall-eq (sum-eq->forall-eq mconstr))]))]))

(define (small-step-forall-eq mconstr)
  ; small step semantics for propogating forall-eq constraints
  (let* ([query (forall-eq-query mconstr)]
         [schema-size (length (extract-schema query))])
    (cond 
      [(query-named? query) mconstr] ; do nothing
      [(query-select? query)
       (let* ([inner-q (query-select-from-query query)]
              [sel-args (query-select-select-args query)]
              [sel-pred (query-select-where-filter query)]
              [inner-q-schema (extract-schema inner-q)]
              [inner-q-schema-size (length (extract-schema inner-q))]
              [inner-q-name-hash (list->hash inner-q-schema)]
              [ref-map (map (lambda (v) (v-from-sql-val v inner-q-name-hash)) sel-args)])
         (forall-eq 
           inner-q
           (c-conj (list (subst-v-ref (forall-eq-constr mconstr) ref-map) 
                         (c-from-sql-filter sel-pred inner-q-name-hash)))))]
      [(query-aggr-general? query)
       (let* ([sel-args (query-aggr-general-select-args query)]
              [where-pred (query-aggr-general-where-filter query)]
              [having-pred (query-aggr-general-having-filter query)]
              [gb-fields (query-aggr-general-gb-fields query)]
              [inner-q (query-aggr-general-query query)]
              [inner-q-schema (extract-schema inner-q)]
              [inner-q-name-hash (list->hash inner-q-schema)]
              [ref-map (map (lambda (v) (v-from-sql-val v inner-q-name-hash)) sel-args)]
              [core-constr (c-conj (list (subst-v-ref (forall-eq-constr mconstr) ref-map) 
                                         (c-from-sql-filter having-pred inner-q-name-hash)
                                         (c-from-sql-filter where-pred inner-q-name-hash)))])
         ; loosing constraints by removing those involving aggregation functions
         (forall-eq inner-q (remove-constr-if-val core-constr contain-aggr-uexpr)))]
      [(query-select-distinct? query)
       (let* ([inner-q (query-select-distinct-from-query query)]
              [sel-args (query-select-distinct-select-args query)]
              [sel-pred (query-select-distinct-where-filter query)]
              [inner-q-schema (extract-schema inner-q)]
              [inner-q-schema-size (length (extract-schema inner-q))]
              [inner-q-name-hash (list->hash inner-q-schema)]
              [ref-map (map (lambda (v) (v-from-sql-val v inner-q-name-hash)) sel-args)])
         (forall-eq 
           inner-q
           (c-conj (list (subst-v-ref (forall-eq-constr mconstr) ref-map) 
                         (c-from-sql-filter sel-pred inner-q-name-hash)))))]
      [(or (query-left-outer-join-2? query)
           (query-left-outer-join? query))
       (let* ([q1 (if (query-left-outer-join-2? query)
                      (query-left-outer-join-2-query1 query)
                      (query-left-outer-join-query1 query))]
              [q2 (if (query-left-outer-join-2? query)
                      (query-left-outer-join-2-query2 query)
                      (query-left-outer-join-query2 query))]
              [q1-schema-size (length (extract-schema q1))]
              [q1-ref-indexes (build-list q1-schema-size values)]
              [q2-schema-size (length (extract-schema q2))]
              [q2-ref-indexes (build-list q2-schema-size (lambda (x) (+ x q1-schema-size)))]
              ; don't forget to update ref indexes for q2
              [q2-ref-update-map (map (lambda (x) (v-ref x))
                                      (append (build-list q1-schema-size values) 
                                              (build-list q2-schema-size values)))])
         (list (forall-eq q1 (remove-constr-if-val 
                               (forall-eq-constr mconstr) 
                               (lambda (x) (contain-out-of-range-v-ref x q1-ref-indexes))))
               (forall-eq q2 (subst-v-ref
                               (remove-constr-if-val 
                                 (forall-eq-constr mconstr)
                                 (lambda (x) (contain-out-of-range-v-ref x q2-ref-indexes)))
                               q2-ref-update-map))))]
      [(query-join? query)
       (let* ([q1 (query-join-query1 query)]
              [q2 (query-join-query2 query)]
              [q1-schema-size (length (extract-schema q1))]
              [q1-ref-indexes (build-list q1-schema-size values)]
              [q2-schema-size (length (extract-schema q2))]
              [q2-ref-indexes (build-list q2-schema-size (lambda (x) (+ x q1-schema-size)))]
              ; don't forget to update ref indexes for q2
              [q2-ref-update-map (map (lambda (x) (v-ref x))
                                      (append (build-list q1-schema-size values) 
                                              (build-list q2-schema-size values)))])
         (list (forall-eq q1 (remove-constr-if-val 
                               (forall-eq-constr mconstr) 
                               (lambda (x) (contain-out-of-range-v-ref x q1-ref-indexes))))
               (forall-eq q2 (subst-v-ref
                               (remove-constr-if-val 
                                 (forall-eq-constr mconstr)
                                 (lambda (x) (contain-out-of-range-v-ref x q2-ref-indexes)))
                               q2-ref-update-map))))]
      [(or (query-rename-full? query) (query-rename? query))
       (let* ([q (cond [(query-rename-full? query) (query-rename-full-query query)]
                       [(query-rename? query) (query-rename-query query)])])
         (forall-eq q (forall-eq-constr mconstr)))]
      [(query-union-all? query)
       (let* ([q1 (query-union-all-query1 query)]
              [q2 (query-union-all-query2 query)])
         (list
           (forall-eq q1 (forall-eq-constr mconstr))
           (forall-eq q2 (forall-eq-constr mconstr))))]
      )))

(define (remove-constr-if-val constr f)
  ; substitutes primitive constraints with (c-true) if any of its value
  ; satisfies the condition specify function f, typed (f::val->bool) 
  (cond
    [(c-primitive? constr)
     (if (or (f (c-primitive-left constr)) (f (c-primitive-right constr)))
       (c-true) ; the primitive pred contains some value satisfying function f
       constr)]
    [(c-true? constr) constr]
    [(c-false? constr) constr]
    [(c-conj? constr) 
     (let ([filtered-content 
             (filter (lambda (c) (not (c-true? c))) 
                     (map (lambda (x) (remove-constr-if-val x f)) 
                          (c-conj-preds constr)))])
       (if (empty? filtered-content) (c-true) (c-conj filtered-content)))]
    [(c-disj? constr) 
     (let ([filtered-content 
             (filter (lambda (c) (not (c-true? c))) 
                     (map (lambda (x) (remove-constr-if-val x f)) 
                          (c-disj-preds constr)))])
       (if (empty? filtered-content) (c-true) (c-disj filtered-content)))]
    [(c-neg? constr) 
     (if (remove-constr-if-val (c-neg-pred constr) f)
       (c-true)
       constr)]))

(define (contain-out-of-range-v-ref v ref-indexes)
  ;; check if the value contain a reference that is outside 
  ;; the range provided by the list ref-indexes
  (cond 
    [(v-uexpr? v) (contain-out-of-range-v-ref (v-uexpr-v v) ref-indexes)]
    [(v-bexpr? v) (or (contain-out-of-range-v-ref (v-bexpr-v1 v) ref-indexes)
                      (contain-out-of-range-v-ref (v-bexpr-v1 v) ref-indexes))]
    [(v-ref? v) (not (index-of ref-indexes (v-ref-id v)))]
    [else #f]))

(define (contain-aggr-uexpr v)
  ;; check whether a value contains aggregation function
  (cond 
    [(v-uexpr? v) (is-aggr-func? (v-uexpr-op v))]
    [(v-bexpr? v) (or (contain-aggr-uexpr (v-bexpr-v1 v))
                      (contain-aggr-uexpr (v-bexpr-v2 v)))]
    [else #f]))

(define (v-from-sql-val v vmap) 
  ; convert sql val expr into meta v expr:
  ; generate a meta constraint v expr from a vmap
  ; vmap maps each column-ref primitive into a v-ref that uses the row id
  (cond
    [(val-const? v) (v-const (val-const-val v))]
    [(val-column-ref? v) (v-ref (hash-ref vmap (val-column-ref-column-name v)))]
    [(val-uexpr? v) (v-uexpr (val-uexpr-op v) (v-from-sql-val (val-uexpr-val v) vmap))]
    [(val-bexpr? v) (v-bexpr (val-bexpr-binop v) 
                             (v-from-sql-val (val-bexpr-v1 v) vmap) 
                             (v-from-sql-val (val-bexpr-v2 v) vmap))]))

(define (c-from-sql-filter f vmap)
  ; generate a meta constraint v expr from a vmap
  ; vmap maps each column-ref primitive into a v-ref that uses the row id
  (cond 
    [(filter-binop? f) (c-primitive (v-from-sql-val (filter-binop-val1 f) vmap)
                                    (filter-binop-op f) 
                                    (v-from-sql-val (filter-binop-val2 f) vmap))]
    [(filter-conj? f) (c-conj (list (c-from-sql-filter (filter-conj-f1 f) vmap)
                                    (c-from-sql-filter (filter-conj-f2 f) vmap)))]
    [(filter-disj? f) (c-disj (list (c-from-sql-filter (filter-disj-f1 f) vmap)
                                    (c-from-sql-filter (filter-disj-f2 f) vmap)))]
    [(filter-not? f) (c-neg (c-from-sql-filter (filter-not-f1 f) vmap))]
    [(filter-true? f) (c-true)]
    [(filter-false? f) (c-false)] ; currently not supporting n-nary filter operation
    ))

(define (subst-v-ref v ref-map)
  ; subst values in the constriant based on ref-map 
  (cond
    [(forall-eq? v) (forall-eq (subst-v-ref (forall-eq-constr v) ref-map))]
    [(sum-eq? v) (sum-eq (sum-eq-queries v) 
                         (subst-v-ref (sum-eq-constr v) ref-map))]
    [(c-primitive? v)
     (c-primitive (subst-v-ref (c-primitive-left v) ref-map) 
                  (c-primitive-op v) 
                  (subst-v-ref (c-primitive-right v) ref-map))]
    [(c-true? v) v]
    [(c-false? v) v]
    [(c-conj? v) (c-conj (map (lambda (x) (subst-v-ref x ref-map)) (c-conj-preds v)))]
    [(c-disj? v) (c-disj (map (lambda (x) (subst-v-ref x ref-map)) (c-disj-preds v)))]
    [(c-neg? v) (c-neg (subst-v-ref (c-neg-pred v) ref-map))]
    [(v-const? v) v]
    [(v-uexpr? v) (v-uexpr (v-uexpr-op v) (subst-v-ref (v-uexpr-v v) ref-map))]
    [(v-bexpr? v) (v-bexpr (subst-v-ref (v-bexpr-v1 v) ref-map) 
                           (v-bexpr-op v) 
                           (subst-v-ref (v-bexpr-v2 v) ref-map))]
    [(v-ref? v) (list-ref ref-map (v-ref-id v))]
    [(v-symval? v) v]
    [else v]))

(define (constr-flatten v)
  ; flattening nested conjunctions into one single conjunction
  (cond
    [(list? v) (map (lambda (x) (constr-flatten x)) v)]
    [(forall-eq? v) (forall-eq (forall-eq-query v) (constr-flatten (forall-eq-constr v)))]
    [(sum-eq? v) (sum-eq (sum-eq-queries v) (constr-flatten (sum-eq-constr v)))]
    [(c-conj? v)
     (let ([content (map (lambda (c) (let ([x (constr-flatten c)])
                                       (if (c-conj? x) (c-conj-preds x) x))) 
                         (c-conj-preds v))])
       (c-conj (flatten content)))]
    [else v]))


(define (merge-forall-eq raw-constraints)
  ; merging constraints 
  (let ([constraints (constr-flatten raw-constraints)])
    (cond [(empty? constraints) (list)]
          [else (let* ([q (forall-eq-query (car constraints))]
                       [t-constrs (filter (lambda (c) (eq? q (forall-eq-query c))) constraints)]
                       [cores (map (lambda (c) (forall-eq-constr c)) t-constrs)]
                       [rest-constrs (filter (lambda (c) (not (eq? q (forall-eq-query c)))) 
                                             (cdr constraints))])
                  (append (list (forall-eq q (c-disj cores)))
                          (merge-forall-eq rest-constrs)))])))

(define (merge-forall-eq-intersect raw-constraints)
  ; merging constraints 
  (define (auto-set-intersect lists)
    ; the helper function to do intersects among lists
    (cond [(empty? lists) (list)]
          [(eq? (length lists) 1) (car lists)]
          [else (set-intersect (car lists) (auto-set-intersect (cdr lists)))]))
  (let ([constraints (constr-flatten raw-constraints)])
    (cond [(empty? constraints) (list)]
          [else (let* ([q (forall-eq-query (car constraints))]
                       [t-constrs (filter (lambda (c) (eq? q (forall-eq-query c))) constraints)]
                       [cores (map (lambda (c) 
                                     (let ([x (forall-eq-constr c)])
                                       (if (c-conj? x) (c-conj-preds x) (list x)))) t-constrs)]
                       [rest-constrs (filter (lambda (c) (not (eq? q (forall-eq-query c)))) 
                                             (cdr constraints))])
                  (append (list (forall-eq q (c-conj (auto-set-intersect cores))))
                          (merge-forall-eq-intersect rest-constrs)))])))



;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;   utility   ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;; 

(define (mconstr-to-hashmap constr-list)
  ; generate a hash map for ease of creating table
  (let ([qname->str 
         (lambda (q) (if (query-named? q) (Table-name (query-named-table-ref q)) "q"))])
    (make-hash
      (map (lambda (x) 
             (cond [(forall-eq? x)
                    (cons (qname->str (forall-eq-query x)) (forall-eq-constr x))])) 
           constr-list))))

(define (queries-to-str queries)
  ; pretty printing tables involved in these constraints
  (let ([f (lambda (q) (cond [(query-named? q) (Table-name (query-named-table-ref q))]
                             [else "q"]))])
    (foldl (lambda (x y) (string-append x "," y)) "" (map f queries))))

(define (to-str v)
  ; pretty printing a constraint
  (cond
    [(list? v) (foldl (lambda (x y) (string-append x "\n" y)) "" 
                      (map (lambda (c) (to-str c)) v))]
    [(forall-eq? v) (format "~a\nForallEQ[~a]" (queries-to-str (list (forall-eq-query v))) 
                            (to-str (forall-eq-constr v)))]
    [(sum-eq? v) (format "~a\nSumEQ[~a]" (queries-to-str (sum-eq-queries v)) 
                         (to-str (sum-eq-constr v)))]
    [(c-primitive? v)
     (format "~a ~a ~a" (to-str (c-primitive-left v)) (c-primitive-op v) 
             (to-str (c-primitive-right v)))]
    [(c-true? v) "#t"]
    [(c-false? v) "#f"]
    [(c-conj? v)
     (let ([content (map (lambda (x) (format "(~a)" (to-str x))) (c-conj-preds v))])
       (if (>= (length content) 1)
           (format "~a" (foldl (lambda (x y) (format "~a \u2227 ~a" x y)) 
                               (car content) (cdr content)))
           ""))]
    [(c-disj? v) 
     (let ([content (map (lambda (x) (to-str x)) (c-disj-preds v))])
       (format "~a" (foldl (lambda (x y) (format "~a \u2228 ~a" x y)) 
                           (car content) (cdr content))))]
    [(c-neg? v) (format "\u00AC ~a" (to-str (c-neg-pred v)))]
    [(v-const? v) (format "~a" (v-const-c v))]
    [(v-uexpr? v) (format "~a ~a" (v-uexpr-op v) (to-str (v-uexpr-v v)))]
    [(v-bexpr? v) (format "~a ~a ~a" (to-str (v-bexpr-v1 v)) (v-bexpr-op v) 
                          (to-str (v-bexpr-v2 v)))]
    [(v-ref? v) (format "r[~a]" (v-ref-id v))]
    [(v-symval? v) (format "@~a" (v-symval-id v))]
    [else v]))
