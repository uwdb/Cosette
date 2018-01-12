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
  (SELECT (VALS "x.origin_city") 
 FROM (AS (NAMED (list-ref tables 3)) ["x"]) 
 WHERE (TRUE) GROUP-BY (list "x.origin_city") 
 HAVING (BINOP (VAL-UNOP aggr-max (val-column-ref "x.actual_time")) < 180)))

(define (q2 tables) 
  (SELECT (VALS "f2.origin_city") 
 FROM (JOIN (AS (NAMED (list-ref tables 3)) ["f2"]) (AS (NAMED (list-ref tables 3)) ["f1"])) 
 WHERE (BINOP "f1.origin_city" = "f2.origin_city") GROUP-BY (list "f2.origin_city") 
 HAVING (BINOP (VAL-UNOP aggr-max (val-column-ref "f1.actual_time")) < 180)))


(define ros-instance (list q1 q2 (list months-info weekdays-info carriers-info flights-info))) 
