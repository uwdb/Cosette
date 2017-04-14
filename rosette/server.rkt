#lang racket/load

(require "cosette.rkt" "util.rkt" "table.rkt" "equal.rkt" "syntax.rkt" "denotation.rkt")
(require json)

;; daemon of the rosette backend
;; if the solver returns a counter example, return the counter example
;; immediately.
;; if the timeout, return the last size of symbolic relations tried 

;; get the commandline arguments
(define args (current-command-line-arguments))

(unless (equal? (vector-length args) 1) (error "require a single filename"))

(define rosfile (vector-ref args 0))

;; max allowed solver time
(define max-time 3)

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
            (define (messenger message) (channel-put main-channel message))
            ; call the solve-queries function
            (match (dynamic-require rosfile 'ros-instance)
              [(list q1 q2 tables) (solve-queries q1 q2 tables messenger)]
              [_ (error "error on loading rosette source code.")])
            )))

;; main thread
(define ret '(1))

(let loop ()
  (define item (channel-get main-channel))
  (case item
    [(timeout) (void)]
    [else (set! ret item) (loop)]))

(displayln ret)

;(displayln (match ret
;             [(n) (jsexpr->string
;                   (hasheq 'status "UNSAT"
;                           'size n))]
;             [_ (cosette-sol->json item)]))
