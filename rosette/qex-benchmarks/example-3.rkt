#lang rosette

(current-bitwidth 10)

(require "../cosette.rkt" "../util.rkt" "../denotation.rkt" 
         "../sql.rkt" "../evaluator.rkt" "../syntax.rkt" "../symmetry.rkt") 

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
    HAVING (BINOP (VAL-UNOP aggr-sum (VAL-BINOP (val-column-ref "O.order_quantity") * (val-column-ref "P.price"))) > (+ val 100))))

(define ros-instance (list q (list product-info orders-info customers-info))) 
(define table-info-list (last ros-instance))
(define table-size-list (make-list (length table-info-list) 2))
(define empty-tables (init-sym-tables table-info-list (build-list (length table-info-list) (lambda (x) 0))))
(define tables (init-sym-tables-from-func table-info-list table-size-list gen-qex-sym-schema))

(define qt (q empty-tables))

(define mconstr (big-step (init-constraint qt) 20))

;(define m-tables (init-sym-tables-from-func table-info-list table-size-list gen-sym-schema))
(define m-tables (init-sym-tables-from-func table-info-list table-size-list gen-qex-sym-schema))
(assert-sym-tables-mconstr m-tables (go-break-symmetry-single qt))



(define (test-now instance tables)
    (let* ([q ((list-ref instance 0) tables)])
      (cosette-check-output-prop q tables (list val) prop-table-empty)))

(time (test-now ros-instance m-tables))
;(time (test-now ros-instance tables))
