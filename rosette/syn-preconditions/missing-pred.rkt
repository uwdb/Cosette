#lang rosette 
 
(require "../cosette.rkt" "../util.rkt" "../table.rkt" 
         "../sql.rkt" "../evaluator.rkt" "../equal.rkt")

(current-bitwidth #f)
 
(define r-info (table-info "r" (list "a" "b" "c")))

(define r (Table "r" (list "a" "b" "c") (gen-sym-schema 3 2)))
 
(define q1 
  (SELECT (VALS "x.b") 
  FROM (NAMED (RENAME r "x")) 
  WHERE (BINOP "x.a" = 5)))

(define q2 
  (SELECT (VALS "x.b") 
  FROM (NAMED (RENAME r "x")) 
  WHERE (BINOP "x.a" < 10)))

(struct table-col (x)
  #:transparent
  #:guard (lambda (x type-name)
            (cond
              [(integer? x) x]
              [else (error "col must be an integer")])))

(define (eval-pred-on-table? table lo op ro)
  (let ([content (filter-zero (Table-content table))]
        [eval-o (lambda (row o)
                  (cond
                    [(table-col? o) (list-ref (car row) (table-col-x o))]
                    [(integer? o) o]
                    [else (error "o can only be a table-col or integer")]))])
    (foldl && #t (map (lambda (x) (op (eval-o x lo) (eval-o x ro))) content)))) 

(define literals (list 1 5 10))

(define operators (list = >))

(define cols (list (table-col 0) (table-col 1) (table-col 2)))

(define (stop-condition i j k lits ops cols)
  (let ([sol
         (begin
           (assert (eval-pred-on-table? r (list-ref lits i) (list-ref ops j) (list-ref cols k)))
           (verify (same q1 q2)))])
    (cond
      [(sat? sol) #f]
      [else (begin (println "find")
                   (println (list (list-ref lits i) (list-ref ops j) (list-ref cols k)))
                   #t)])))


; do the search here
(time
(for* ([i (in-range (length literals))]
       [j (in-range (length operators))]
       [k (in-range (length cols))])
       #:break (stop-condition i j k literals operators cols)
       (clear-asserts!)
       (println (list i j k))
 ))
