#lang rosette

(current-bitwidth #f)

(require "../cosette.rkt" "../util.rkt" "../denotation.rkt" 
         "../sql.rkt" "../evaluator.rkt" "../syntax.rkt" "../symmetry.rkt"
         "../table.rkt") 

(provide ros-instance)

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

(define ros-instance (list q (list product-info orders-info customers-info) (list) prop-table-empty)) 