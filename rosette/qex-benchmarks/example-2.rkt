#lang rosette

(current-bitwidth #f)

(require "../cosette.rkt" "../util.rkt" "../denotation.rkt" 
         "../sql.rkt" "../evaluator.rkt" "../syntax.rkt" "../symmetry.rkt") 

(define product-info (table-info "P" (list "id" "name" "price")))
(define orders-info (table-info "O" (list "order_id" "customer_id")))
(define customers-info (table-info "C" (list "customer_id" "name")))

; SELECT C.CustomerID, Count(O.OrderID)
; FROM Orders AS O
; JOIN Customers AS C ON
; O.CustomerID = C.CustomerID
; GROUP BY C.CustomerID HAVING
; Count(O.OrderID) > 1

(define (q tables)
   (SELECT (VALS "C.customer_id" (VAL-UNOP aggr-max (val-column-ref "O.order_id")))
    FROM  (JOIN (NAMED (list-ref tables 2)) (NAMED (list-ref tables 1)))
    WHERE (BINOP "O.customer_id" = "C.customer_id") 
    GROUP-BY (list "C.customer_id")         
    HAVING (BINOP (VAL-UNOP aggr-max (val-column-ref "O.order_id")) > 1)))

(define ros-instance (list q (list product-info orders-info customers-info))) 
(define table-info-list (last ros-instance))
(define table-size-list (make-list (length table-info-list) 5))
(define empty-tables (init-sym-tables table-info-list (build-list (length table-info-list) (lambda (x) 0))))
(define tables (init-sym-tables-from-func table-info-list table-size-list gen-qex-sym-schema))

(define qt (q empty-tables))

(define mconstr (big-step (init-constraint qt) 20))

;(define m-tables (init-sym-tables-from-func table-info-list table-size-list gen-sym-schema))
(define m-tables (init-sym-tables-from-func table-info-list table-size-list gen-qex-sym-schema))

(displayln (to-str mconstr))
(displayln "--")
(displayln (to-str (remove-unused-constr mconstr)))
(displayln "--")
(assert-sym-tables-mconstr m-tables (go-break-symmetry-single qt))

(define (test-now instance tables)
    (let* ([q ((list-ref instance 0) tables)])
      (cosette-check-output-prop q tables (list) prop-table-empty)))



;(time (test-now ros-instance m-tables))
;(time (test-now ros-instance tables))