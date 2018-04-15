#lang rosette 
 
(require "../cosette.rkt" "../sql.rkt" "../evaluator.rkt" "../syntax.rkt") 
 
(provide ros-instance)
 
(current-bitwidth #f)
 
(define-symbolic div_ (~> integer? integer? integer?))
 
(define months-info (table-info "months" (list "mid" "month")))
 
(define weekdays-info (table-info "weekdays" (list "did" "day_of_week")))
 
(define carriers-info (table-info "carriers" (list "cid" "name")))
 
(define flights-info (table-info "flights" (list "fid" "year" "month_id" "day_of_month" "day_of_week_id" "carrier_id" "flight_num" "origin_city" "origin_state" "dest_city" "dest_state" "departure_delay" "taxi_out" "arrival_delay" "canceled" "actual_time" "distance" "capacity" "price")))
 

(define (q1 tables) 
  (SELECT (VALS "c.name") 
 FROM (JOIN (AS (NAMED (list-ref tables 2)) ["c"]) (AS (NAMED (list-ref tables 3)) ["f"])) 
 WHERE (BINOP "c.cid" = "f.carrier_id") GROUP-BY (list "c.cid" "c.name" "f.year" "f.month_id" "f.day_of_month") 
 HAVING (BINOP (VAL-UNOP aggr-count (val-column-ref "f.fid")) > 1000)))

(define (q2 tables) 
  (SELECT (VALS "c.name") 
 FROM (JOIN (AS (NAMED (list-ref tables 3)) ["f"]) (JOIN (AS (NAMED (list-ref tables 2)) ["c"]) (AS (NAMED (list-ref tables 1)) ["w"]))) 
 WHERE (AND (BINOP "f.carrier_id" = "c.cid") (BINOP "f.day_of_week_id" = "w.did")) GROUP-BY (list "c.name" "f.year" "f.month_id" "f.day_of_month") 
 HAVING (BINOP (VAL-UNOP aggr-count (val-column-ref "w.did")) > 1000)))


(define ros-instance (list q1 q2 (list months-info weekdays-info carriers-info flights-info))) 
