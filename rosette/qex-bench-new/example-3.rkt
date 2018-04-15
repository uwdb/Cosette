#lang rosette

(current-bitwidth 10)

(require "../cosette.rkt" "../util.rkt" "../denotation.rkt" 
         "../sql.rkt" "../evaluator.rkt" "../syntax.rkt" "../symmetry.rkt") 

(provide ros-instance)

(define product-info (table-info "P" (list "id" "name" "price")))
(define orders-info (table-info "O" (list "order_id" "customer_id" "order_quantity" "product_id")))
(define customers-info (table-info "C" (list "customer_id" "name")))

(define-symbolic* val integer?)

; DECLARE @value AS INT;
; SELECT C.CustomerID, SUM(OP.OrderProductQuantity * P.ProductPrice)
; Orders AS O 
; JOIN Products AS P ON O.ProductID = P.ProductID
; JOIN Customers AS C ON O.CustomerID = C.CustomerID
; WHERE @value > 1
; GROUP BY C.CustomerID
; HAVING SUM(OP.OrderProductQuantity * P.ProductPrice) > 100 + @value

(define (q tables)
   (SELECT (VALS "C.customer_id" (VAL-UNOP aggr-sum (VAL-BINOP (val-column-ref "O.order_quantity") * (val-column-ref "P.price"))))
    FROM  (JOIN (JOIN (NAMED (list-ref tables 2)) (NAMED (list-ref tables 1))) (NAMED (list-ref tables 0)))
    WHERE (AND (AND (BINOP "O.product_id" = "P.id") (BINOP "O.customer_id" = "C.customer_id")) (BINOP val > 1))
    GROUP-BY (list "C.customer_id")         
    HAVING (AND (BINOP (COUNT-DISTINCT "O.order_quantity") > 3)
    			(BINOP (VAL-UNOP aggr-sum (VAL-BINOP (val-column-ref "O.order_quantity") * (val-column-ref "P.price"))) > (+ val 100)))))

(define ros-instance (list q (list product-info orders-info customers-info) (list val) prop-table-empty)) 