#lang rosette

(require "symmetry.rkt" "cosette.rkt")

(provide experiment) 

(define symbreak #t)

(define (experiment ros-instance)
  (displayln (format "[[symbreak]] ~a\n" symbreak))
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
                     (time-apply go-break-symmetry-bounded (list qt1 qt2))])
        (displayln (format "[inference time] ~a" t-real))
        (display (to-str mconstr))
        (car mconstr))))
  (define (test-now instance table-size-list)
      (displayln "[[Start]]")
      (displayln (format "[table size] ~a" table-size-list))
      (let* ([tables (init-sym-tables table-info-list table-size-list)]
             [qt1 (fq1 tables)]
             [qt2 (fq2 tables)])
        (cosette-solve qt1 qt2 tables)))
  (define (test-now-mconstr instance table-size-list)
      (displayln "[[Start]]")
      (displayln (format "[table size] ~a" table-size-list))
      (asserts)
      (let* ([tables (init-sym-tables-mconstr table-info-list table-size-list mconstr)]
             [qt1 (fq1 tables)]
             [qt2 (fq2 tables)])
        (cosette-solve qt1 qt2 tables)))
  (define (test-loop table-size-list test-func)
    (let*-values ([(sol t-cpu t-real t-gc) 
                   (time-apply test-func (list ros-instance table-size-list))])
      (cond [(eq? (car (car sol)) "NEQ") 
             (displayln (format "[real time] ~a ms" t-real))
             (pretty-display (cdr (car sol)))
             (displayln "[[End]]\n")]
            [else 
             (displayln (format "[real time] ~a ms" t-real))
             (displayln (car sol))
             (displayln "[[End]]\n")
             (flush-output)
             (test-loop (inc-table-size-list table-size-list) test-func)])))
  (if symbreak
      (test-loop initial-table-size-list test-now-mconstr)
      (test-loop initial-table-size-list test-now)))


