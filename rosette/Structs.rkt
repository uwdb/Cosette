#lang rosette/safe
(require racket/generic)
(require racket/match)

(define-generics table-gen
  (get-col table-gen col-name)
  (set-col table-gen col-name val))

(define-generics query-gen
  (run-query query-gen table))

(struct SymTable ([columns #:mutable])
  #:transparent
  #:methods gen:table-gen
  [(define (get-col self col-name)
     (match-define (SymTable columns) self)
     (cadr (assoc col-name columns)))
   
   (define (set-col self col-name val)
     (match-define (SymTable columns) self)
     (map (lambda (p)
            (if (eq? (car p) col-name)
                (list (car p) val)
                p))
          columns))
   ])

(define (init-symtable col-names-types)
  (let ([columns (map (lambda (p)
                        (let ([name (car p)]
                              [type (cadr p)])
                          (define-symbolic* col type) 
                          (list name col)))
                      col-names-types)])
    (SymTable columns)))

;; here select should be lambda on table,
;; where should be predicates
(struct Query (select where)
  #:transparent
  #:methods gen:query-gen
  [(define (run-query self table)
     (match-define (Query select where) self)
     (if (where table) (select table) '()))
   ])

(define my-query
  (Query (lambda (t)
           (let ([c0 (get-col t 'c1)]
                 [c1 (get-col t 'c2)]
                 [c2 (get-col t 'c3)])
             (list (+ c1 c2) (+ c2 c0))))
         (lambda (t)
           (let ([c0 (get-col t 'c1)]
                 [c1 (get-col t 'c2)]
                 [c2 (get-col t 'c3)])
             (and (> c1 c0) (< c1 c2))))))

(define my-query2
  (Query (lambda (t)
           (let ([c0 (get-col t 'c1)]
                 [c1 (get-col t 'c2)]
                 [c2 (get-col t 'c3)])
             (list (+ c1 c2) (+ c2 c0))))
         (lambda (t)
           (let ([c0 (get-col t 'c1)]
                 [c1 (get-col t 'c2)]
                 [c2 (get-col t 'c3)])
             (and (<= c0 c1) (> c2 c1))))))

(define sym-table
  (init-symtable `((c1 ,integer?) (c2 ,integer?) (c3 ,integer?))))

(verify (assert (eq? (run-query my-query sym-table) (run-query my-query2 sym-table))))