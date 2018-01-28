#lang rosette

(require "symmetry.rkt" "cosette.rkt")

(provide run-experiment) 

(define symbreak #t)
(define simplify-constr #f)

(define (run-experiment ros-instance)
  (displayln (format "[[symbreak]] ~a" symbreak))
  (define symbreak-func (if simplify-constr go-break-symmetry-bounded-intersect go-break-symmetry-bounded))
  (define fq1 (list-ref ros-instance 0))
  (define fq2 (list-ref ros-instance 1))
  (define table-info-list (last ros-instance))
  (define initial-table-size-list (init-table-size-list (list fq1 fq2) table-info-list))
  (define mconstr
    (let* ([empty-tables 
            (init-sym-tables table-info-list 
                             (build-list (length table-info-list) (lambda (x) 0)))]
           [qt1 (fq1 empty-tables)]
           [qt2 (fq2 empty-tables)])
      (let*-values ([(mconstr t-cpu t-real t-gc) 
                     (time-apply symbreak-func (list qt1 qt2))])
        (displayln (format "[inference time] ~a" t-real))
        (displayln "[constraint]")
        (display (to-str mconstr))
        (displayln "--------------------")
        (car mconstr))))
  (define (test-now instance table-size-list)
      (let* ([tables (init-sym-tables table-info-list table-size-list)]
             [qt1 (fq1 tables)]
             [qt2 (fq2 tables)])
        (cosette-solve qt1 qt2 tables)))
  (define (test-now-mconstr instance table-size-list)
      (let* ([tables (init-sym-tables-mconstr table-info-list table-size-list mconstr)]
             [qt1 (fq1 tables)]
             [qt2 (fq2 tables)])
        (cosette-solve qt1 qt2 tables)))
  (define (test-loop table-size-list test-func)
    (let*-values ([(sol t-cpu t-real t-gc) 
                   (time-apply test-func (list ros-instance table-size-list))])
      (cond [(eq? (car (car sol)) "NEQ") 
             (displayln (format "[table size] ~a [real time] ~a ms" table-size-list t-real))
             (pretty-display (cdr (car sol)))
             (displayln "")]
            [else 
             (displayln (format "[table size] ~a [real time] ~a ms" table-size-list t-real))
             (flush-output)
             (test-loop (inc-table-size-list table-size-list) test-func)])))
  (if symbreak
      (test-loop initial-table-size-list test-now-mconstr)
      (test-loop initial-table-size-list test-now)))


