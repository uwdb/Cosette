#lang rosette 
 
(require "../cosette.rkt" "../sql.rkt" "../evaluator.rkt" "../syntax.rkt") 
 
(provide ros-instance)
 
(current-bitwidth #f)
 
(define-symbolic div_ (~> integer? integer? integer?))
 
(define months-info (table-info "months" (list "mid" "month")))
 
(define weekdays-info (table-info "weekdays" (list "did" "day_of_week")))
 
(define carriers-info (table-info "carriers" (list "cid" "name")))
 
(define flights-info (table-info "flights" (list "fid" "year" "month_id" "day_of_month" "day_of_week_id" "carrier_id" "flight_num" "origin_city" "origin_state" "dest_city" "dest_state" "departure_delay" "taxi_out" "arrival_delay" "canceled" "actual_time" "distance" "capacity" "price")))
 
(define-symbolic* str_washington_ integer?) 
(define-symbolic* str_seattle_wa_ integer?) 

(define (q1 tables) 
  (SELECT (VALS "c.name" (VAL-BINOP (VAL-UNOP aggr-sum (val-column-ref "f.canceled")) div_ (VAL-UNOP aggr-count (val-column-ref "c.cid")))) 
 FROM (JOIN (NAMED (RENAME (list-ref tables 3) "f")) (NAMED (RENAME (list-ref tables 2) "c"))) 
 WHERE (AND (BINOP "c.cid" = "f.carrier_id") (BINOP "f.origin_city" = str_seattle_wa_)) GROUP-BY (list "c.cid" "c.name") 
 HAVING (BINOP (VAL-BINOP (VAL-UNOP aggr-sum (val-column-ref "f.canceled")) div_ (VAL-UNOP aggr-count (val-column-ref "c.cid"))) > (VAL-BINOP 5 div_ 1000))))

(define (q2 tables) 
  (SELECT (VALS "c.name" (VAL-BINOP (VAL-UNOP aggr-sum (val-column-ref "f.canceled")) div_ (VAL-UNOP aggr-count (val-column-ref "f.canceled")))) 
 FROM (JOIN (NAMED (RENAME (list-ref tables 3) "f")) (NAMED (RENAME (list-ref tables 2) "c"))) 
 WHERE (AND (BINOP "f.carrier_id" = "c.cid") (AND (BINOP "f.origin_city" = str_seattle_wa_) (BINOP "f.origin_state" = str_washington_))) GROUP-BY (list "c.name") 
 HAVING (BINOP (VAL-BINOP (VAL-UNOP aggr-sum (val-column-ref "f.canceled")) div_ (VAL-UNOP aggr-count (val-column-ref "f.canceled"))) > (VAL-BINOP 5 div_ 1000))))


(define ros-instance (list q1 q2 (list months-info weekdays-info carriers-info flights-info))) 
