#lang rosette

(require "symmetry.rkt" "cosette.rkt" "syntax.rkt" "util.rkt")

(provide run-experiment
         run-qex-experiment) 

(define (run-experiment ros-instance symbreak simplify-constr qex-encoding)
  (displayln (format "[[config]] symbreak:~a, simplify-constr:~a, qex-encoding:~a" 
                     symbreak simplify-constr qex-encoding))
  (define symbreak-func ;the symmetry breaking function
    (if simplify-constr 
        go-break-symmetry-bounded-intersect 
        go-break-symmetry-bounded))
  (define table-init-func ;the function used to define symbolic tables
    (if qex-encoding gen-qex-sym-schema gen-sym-schema))
  (define fq1 (list-ref ros-instance 0))
  (define fq2 (list-ref ros-instance 1))
  (define table-info-list (last ros-instance))
  (define initial-table-size-list (init-table-size-list (list fq1 fq2) table-info-list))
  (define mconstr
    (let* ([empty-tables 
            (init-sym-tables table-info-list (build-list (length table-info-list) (lambda (x) 0)))]
           [qt1 (fq1 empty-tables)]
           [qt2 (fq2 empty-tables)])
      (let*-values ([(mconstr t-cpu t-real t-gc) 
                     (time-apply symbreak-func (list qt1 qt2))])
        (displayln (format "[inference time] ~a" t-real))
        (displayln "[constraint]")
        (display (to-str mconstr))
        (displayln (format "[query size] ~a ~a" (query-size qt1) (query-size qt2)))
        (displayln (format "[query aggr] ~a ~a" (query-contain-aggr qt1) (query-contain-aggr qt2)))
        (displayln "--------------------")
        (car mconstr))))
  (define (test-now instance table-size-list)
      (let* ([tables (init-sym-tables-from-func table-info-list table-size-list table-init-func)]
             [qt1 (fq1 tables)]
             [qt2 (fq2 tables)])
        (if symbreak (assert-sym-tables-mconstr tables mconstr) (list))
        (cosette-solve qt1 qt2 tables)))
  (define (test-loop table-size-list test-func)
    (let*-values ([(sol t-cpu t-real t-gc) 
                   (time-apply test-func (list ros-instance table-size-list))])
      (cond [(eq? (car (car sol)) "NEQ")
             (displayln "[NEQ]")
             (displayln (format "[table size] ~a [real time] ~a ms" table-size-list t-real))
             (pretty-display (cdr (car sol)))
             (displayln "")
             (flush-output)]
            [else 
             (displayln (format "[table size] ~a [real time] ~a ms" table-size-list t-real))
             (flush-output)
             (test-loop (inc-table-size-list table-size-list) test-func)])))
  (test-loop initial-table-size-list test-now))


(define (run-qex-experiment ros-instance symbreak qex-encoding)
  (displayln (format "[[config]] symbreak:~a, qex-encoding:~a" symbreak qex-encoding))
  (define symbreak-func go-break-symmetry-single)
  (define table-init-func ;the function used to define symbolic tables
    (if qex-encoding gen-qex-sym-schema gen-sym-schema))
  (define fq (list-ref ros-instance 0))
  (define table-info-list (list-ref ros-instance 1))
  (define extra-variable-list (list-ref ros-instance 2))
  (define check-prop (list-ref ros-instance 3))
  (define initial-table-size-list (init-table-size-list (list fq) table-info-list))
  (define mconstr
    (let* ([empty-tables 
            (init-sym-tables table-info-list (build-list (length table-info-list) (lambda (x) 0)))]
           [qt (fq empty-tables)])
      (let*-values ([(mconstr t-cpu t-real t-gc) 
                     (time-apply symbreak-func (list qt))])
        (displayln (format "[inference time] ~a" t-real))
        (displayln "[constraint]")
        (display (to-str mconstr))
        (displayln (format "[query size] ~a" (query-size qt)))
        (displayln (format "[query aggr] ~a" (query-contain-aggr qt)))
        (displayln "--------------------")
        (car mconstr))))
  (define (test-now instance table-size-list)
      (let* ([tables (init-sym-tables-from-func table-info-list table-size-list table-init-func)]
             [qt (fq tables)])
        (if symbreak (assert-sym-tables-mconstr tables mconstr) (list))
        (cosette-check-output-prop qt tables extra-variable-list prop-table-empty)))
  (define (test-loop table-size-list test-func)
    (let*-values ([(sol t-cpu t-real t-gc) 
                   (time-apply test-func (list ros-instance table-size-list))])
      (cond [(eq? (car (car sol)) "NEQ")
             (displayln "[NEQ]")
             (displayln (format "[table size] ~a [real time] ~a ms" table-size-list t-real))
             (pretty-display (cdr (car sol)))
             (displayln "")
             (flush-output)
             (test-loop (inc-table-size-list table-size-list) test-func)]
            [else 
             (displayln (format "[table size] ~a [real time] ~a ms" table-size-list t-real))
             (flush-output)
             (test-loop (inc-table-size-list table-size-list) test-func)])))
  (test-loop initial-table-size-list test-now))


;; query: the sql query to extract schema for
(define (query-size query)
  (cond 
    [(query-named? query) 1]
    [(query-join? query) 
     (+ (query-size (query-join-query1 query)) 
        (query-size (query-join-query2 query))
        1)]
    [(query-rename? query)
     (query-size (query-rename-query query))]
    [(query-rename-full? query)
     (query-size (query-rename-full-query query))]
    [(query-select? query)
     (+ 1 (query-size (query-select-from-query query)))]
    [(query-select-distinct? query)
     (+ 1 (query-size (query-select-distinct-from-query query)))]
    [(query-aggr-general? query)
     (+ 1 (query-size (query-aggr-general-query query)))]
    [(query-union-all? query) 
     (+ (query-size (query-union-all-query1 query))
        (query-size (query-union-all-query2 query))
        1)]))

;; query: the sql query to extract schema for
(define (query-contain-aggr query)
  (cond 
    [(query-named? query) #f]
    [(query-join? query) 
     (or (query-contain-aggr (query-join-query1 query)) 
         (query-contain-aggr (query-join-query2 query)))]
    [(query-rename? query)
     (query-contain-aggr (query-rename-query query))]
    [(query-rename-full? query)
     (query-contain-aggr (query-rename-full-query query))]
    [(query-select? query)
     (query-contain-aggr (query-select-from-query query))]
    [(query-select-distinct? query)
     (query-contain-aggr (query-select-distinct-from-query query))]
    [(query-aggr-general? query) #t]
    [(query-union-all? query) 
     (or (query-contain-aggr (query-union-all-query1 query))
         (query-contain-aggr (query-union-all-query2 query)))]))

