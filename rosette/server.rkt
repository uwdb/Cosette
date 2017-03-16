#lang rosette

;; daemon of the rosette backend
;; if the solver returns a counter example, return the counter example
;; immediately.
;; if the timeout, return the last size of symbolic relations tried 

(define max-time 3)

;; the channel that the main thread receives, the message could either be an
;; counter example, or a timeout message from the timing threads
(define main-channel (make-channel))

;; the timing thread, will send timeout message to report thread
(define timing-thread
  (thread (lambda ()
            (sleep max-time)
            (channel-put main-channel 'timeout))))

;; the (fake) solver thread
;; at each iteration, if unsat, it will send sizes fo relations to main thread 
;; and proceed to the next iteration (increase the sizes of symbolic relations)
;; if a counterexample is found, it will return the counterexample immediately.
(define solver-thread
  (thread (lambda ()
            (sleep 4)
            (channel-put main-channel "UNSAT"))))

;; main thread
(define item (channel-get main-channel))
(define ret 'init)
(case item
  [(timeout)
   (void)]
  [else
   (set! ret item)])

(displayln item)
