#lang rosette

(current-bitwidth #f)

(require "../cosette.rkt" "../util.rkt" "../denotation.rkt" 
         "../sql.rkt" "../evaluator.rkt" "../syntax.rkt" "../symmetry.rkt") 

(provide ros-instance)

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
   (SELECT (VALS "C.customer_id" (VAL-UNOP aggr-count (val-column-ref "O.order_id")))
    FROM  (JOIN (NAMED (list-ref tables 2)) (NAMED (list-ref tables 1)))
    WHERE (BINOP "O.customer_id" = "C.customer_id") 
    GROUP-BY (list "C.customer_id")         
    HAVING (BINOP (COUNT-DISTINCT "O.order_id") > 8)))

(define ros-instance (list q (list product-info orders-info customers-info) (list) prop-table-empty)) 