#lang rosette 
 
(require "../cosette.rkt" "../sql.rkt" "../evaluator.rkt" "../syntax.rkt") 
 
(provide ros-instance)
 
(current-bitwidth #f)
 
(define-symbolic div_ (~> integer? integer? integer?))
 
(define months-info (table-info "months" (list "mid" "month")))
 
(define weekdays-info (table-info "weekdays" (list "did" "day_of_week")))
 
(define carriers-info (table-info "carriers" (list "cid" "name")))
 
(define flights-info (table-info "flights" (list "fid" "year" "month_id" "day_of_month" "day_of_week_id" "carrier_id" "flight_num" "origin_city" "origin_state" "dest_city" "dest_state" "departure_delay" "taxi_out" "arrival_delay" "canceled" "actual_time" "distance" "capacity" "price")))
 
(define-symbolic* str_new_york_ny_ integer?) 
(define-symbolic* str_seattle_wa_ integer?) 

(define (q1 tables) 
  (SELECT (VALS "c.name" (VAL-BINOP (VAL-UNOP aggr-sum (val-column-ref "f.price")) div_ (VAL-UNOP aggr-count (val-column-ref "f.price")))) 
 FROM (JOIN (AS (NAMED (list-ref tables 3)) ["f"]) (AS (NAMED (list-ref tables 2)) ["c"])) 
 WHERE (AND (BINOP "f.carrier_id" = "c.cid") (OR (AND (BINOP "f.origin_city" = str_seattle_wa_) (BINOP "f.dest_city" = str_new_york_ny_)) (AND (BINOP "f.origin_city" = str_new_york_ny_) (BINOP "f.dest_city" = str_seattle_wa_)))) GROUP-BY (list "c.cid" "c.name") 
 HAVING (TRUE)))

(define (q2 tables) 
  (SELECT (VALS "c.name" (VAL-BINOP (VAL-UNOP aggr-sum (val-column-ref "f.price")) div_ (VAL-UNOP aggr-count (val-column-ref "f.price")))) 
 FROM (JOIN (AS (NAMED (list-ref tables 3)) ["f"]) (AS (NAMED (list-ref tables 2)) ["c"])) 
 WHERE (AND (BINOP "f.carrier_id" = "c.cid") (AND (BINOP "f.origin_city" = str_seattle_wa_) (BINOP "f.dest_city" = str_new_york_ny_))) GROUP-BY (list "c.name" "f.month_id") 
 HAVING (TRUE)))


(define ros-instance (list q1 q2 (list months-info weekdays-info carriers-info flights-info))) 
