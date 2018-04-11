#lang rosette

(current-bitwidth #f)

(require "../cosette.rkt" "../util.rkt" "../denotation.rkt" 
         "../sql.rkt" "../evaluator.rkt" "../syntax.rkt" "../symmetry.rkt"
         "../table.rkt") 

(define product-info (table-info "P" (list "id" "name" "price")))
(define orders-info (table-info "O" (list "order_id" "customer_id")))
(define customers-info (table-info "C" (list "customer_id" "name")))

; SELECT C.CustomerID, O.OrderID
; FROM Orders AS O
; JOIN Customers AS C ON
; O.CustomerID = C.CustomerID
; WHERE O.CustomerID > 2 AND
; O.OrderID < 15

(define (q tables)
   (SELECT (VALS "C.customer_id" "O.order_id")
    FROM  (JOIN (NAMED (list-ref tables 2)) (NAMED (list-ref tables 1)))
    WHERE (AND (BINOP "O.customer_id" = "C.customer_id") 
               (AND (BINOP "O.customer_id" > 2) (BINOP "O.order_id" < 15)))))

(define ros-instance (list q (list product-info orders-info customers-info))) 

(define table-info-list (last ros-instance))
(define table-size-list (make-list (length table-info-list) 10))
(define empty-tables (init-sym-tables table-info-list (build-list (length table-info-list) (lambda (x) 0))))
(define tables (init-sym-tables-from-func table-info-list table-size-list gen-qex-sym-schema))

(define qt (q empty-tables))

(define mconstr (big-step (init-constraint qt) 20))

;(define m-tables (init-sym-tables-from-func table-info-list table-size-list gen-sym-schema))
(define m-tables (init-sym-tables-from-func table-info-list table-size-list gen-qex-sym-schema))
(assert-sym-tables-mconstr m-tables (go-break-symmetry-single qt))

(define (test-now instance tables)
    (let* ([q ((list-ref instance 0) tables)])
      (cosette-check-output-prop q tables (list) prop-table-empty)))

(time (test-now ros-instance m-tables))
;(time (test-now ros-instance tables))

