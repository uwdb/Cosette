#lang rosette 
 
(require "../cosette.rkt" "../util.rkt" "../table.rkt" 
         "../sql.rkt" "../evaluator.rkt" "../equal.rkt") 
 
(current-bitwidth #f)
 
(define dept-info (table-info "dept" (list "dept" "loc" "mgr")))
 
(define emp-info (table-info "emp" (list "name" "dept" "emp")))

(define s-dept (Table "dept" (list "dept" "loc" "mgr") (gen-sym-schema 3 2)))

(define s-emp (Table "emp" (list "name" "dept" "emp") (gen-sym-schema 3 2)))

(define c-dept (Table "dept" (list "dept" "loc" "mgr")
                      (list (cons (list 0 3 0) 1)
                            (cons (list 0 3 0) 1))))

(define c-emp (Table "emp" (list "name" "dept" "emp")
                     (list (cons (list 42 0 0) 1)
                           (cons (list 43 1 0) 1))))

(define emp s-emp)

(define dept s-dept)
 
(define q1 
  (SELECT (VALS "x.name") 
  FROM (NAMED (RENAME emp "x")) 
  WHERE (EXISTS (AS (SELECT (VALS "y.dept" "y.loc" "y.mgr") 
                            FROM (NAMED (RENAME dept "y")) 
                            WHERE (AND (AND (BINOP "y.loc" = 3)
                                            (BINOP "x.emp" = "y.mgr"))
                                       (BINOP "x.dept" = "y.dept"))) ["anyname" (list "dept" "loc" "mgr")]))))

(define q2 
  (SELECT (VALS "x.name") 
  FROM (JOIN (NAMED (RENAME emp "x")) (NAMED (RENAME dept "y"))) 
  WHERE (AND (AND (BINOP "x.dept" = "y.dept") (BINOP "y.loc" = 3)) (BINOP "x.emp" = "y.mgr"))))

; when 
;(assert-table-col-distinct emp (list 2))
;(assert-table-col-distinct dept (list 0))

(define-symbolic* e1 e2 e3 integer?)

(define-symbolic* d1 d2 d3 integer?)

(assert (and (>= e1 0) (< e1 3)))
(assert (and (>= e2 0) (< e2 3)))
(assert (and (>= e3 0) (< e3 3)))
(assert (and (>= d1 0) (< d1 3)))
(assert (and (>= d2 0) (< d2 3)))
(assert (and (>= d3 0) (< d3 3)))

;(require rosette/lib/angelic)
;(define ec (choose* (list) (list e1) (list e1 e2) (list e1 e2 e3)))
;(define dc (choose* (list) (list d1) (list d1 d2) (list d1 d2 d3)))

(define ec (list e1 e2 e3))
(define dc (list d1 d2 d3))

;(assert-table-cols-distinct emp ec)
;(assert-table-cols-distinct dept dc)

;(optimize #:minimize (list (+ (length ec) (length dc)))
;          #:guarantee (assert (forall (list s-emp s-dept) (same q1 q2))))
(define (init-key-size table-num)
  (make-list table-num 0))

(define (inc-key-size key-size)
  (match key-size
         [(list x) (list (+ x 1))]
         [(cons x l)
          (cond [(< x (car l)) (append (list (+ x 1)) l)]
                [else (append (list x) (inc-key-size l))])]))

;(optimize #:minimize (list (+ (length ec) (length dc)))
;          #:guarantee (assert (forall (list s-emp s-dept) (same q1 q2))))

#; (synthesize #:forall (list s-emp s-dept)
            #:guarantee (assert (same q1 q2)))

;incremental search with increasing key size, once found, return the result
(define (search-key-constraints input-tables keys key-size)
  ; assertion of key-sizes
  (for ([i (in-range (length input-tables))])
          (assert-table-cols-distinct
           (list-ref input-tables i)
           (take (list-ref keys i) (list-ref key-size i))))
     (assert (and (>= e1 0) (< e1 3)))
     (assert (and (>= e2 0) (< e2 3)))
     (assert (and (>= e3 0) (< e3 3)))
     (assert (and (>= d1 0) (< d1 3)))
     (assert (and (>= d2 0) (< d2 3)))
     (assert (and (>= d3 0) (< d3 3)))
     (define sol (synthesize #:forall input-tables
                             #:guarantee (assert (same q1 q2))))
     (cond [(sat? sol) (list sol key-size)]
           [(eq? (car key-size) (length input-tables)) '('UNSAT)]
           [else (begin
                   (clear-asserts!)
                   (search-key-constraints input-tables keys (inc-key-size key-size)))]))

(define input-tables (list s-emp s-dept))

(define keys (list ec dc))

(define sol (search-key-constraints input-tables (list ec dc) (list 0 0)))

(if (sat? (car sol)) 
    (for/list ([i (in-range (length keys))])
      (take (evaluate (list-ref keys i) (car sol)) (list-ref (cadr sol) i)))
    "UNSAT")
