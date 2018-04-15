#lang racket/load

(require "cosette.rkt" "util.rkt" "table.rkt" 
         "equal.rkt" "syntax.rkt" "denotation.rkt"
         "test-util.rkt")
(require json)

;; daemon of the rosette backend
;; if the solver returns a counter example, return the counter example
;; immediately.
;; if the timeout, return the last size of symbolic relations tried 

;; get the commandline arguments
(define args (current-command-line-arguments))
(unless (> (vector-length args) 2) 
  (error "[Error] Usage: racket qex-test-server.rkt file_name max-time [--symbreak] [--qex-enc]"))
(define rosfile (vector-ref args 0))
(define max-time (string->number (vector-ref args 1)))

(define symbreak (if (equal? (vector-member "--symbreak" args) #f) #f #t))
(define qex-encoding (if (equal? (vector-member "--qex-enc" args) #f) #f #t))

    
;; the channel that the main thread receives, the message could either be an
;; counter example, or a timeout message from the timing threads
(define main-channel (make-channel))

;; the timing thread, will send timeout message to report thread
(define timing-thread
  (thread (lambda ()
            (sleep max-time)
            (channel-put main-channel 'timeout))))

;; the solver thread
;; at each iteration, if unsat, it will send sizes fo relations to main thread 
;; and proceed to the next iteration (increase the sizes of symbolic relations)
;; if a counterexample is found, it will return the counterexample immediately.
(define solver-thread
  (thread (lambda ()
            ; call the solve-queries function
            (match (dynamic-require rosfile 'ros-instance)
              [(list fq1 tables extra-symvals check-prop) 
               (run-qex-experiment (list fq1 tables extra-symvals check-prop) symbreak qex-encoding)
               (channel-put main-channel 'timeout)]
              [_ (error "error on loading rosette source code.")])
            )))

;; main thread
(define ret '(1))

(let loop () 
  (define item (channel-get main-channel))
  (case item
    [(timeout) (void)]
    [else (set! ret item) (loop)]))

