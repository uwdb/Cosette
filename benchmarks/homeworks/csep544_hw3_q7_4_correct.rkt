#lang rosette 
 
(require "../cosette.rkt" "../sql.rkt" "../evaluator.rkt" "../syntax.rkt") 
 
(provide ros-instance)
 
(current-bitwidth #f)
 
(define-symbolic div_ (~> integer? integer? integer?))
 
(define months-info (table-info "months" (list "mid" "month")))
 
(define weekdays-info (table-info "weekdays" (list "did" "day_of_week")))
 
(define carriers-info (table-info "carriers" (list "cid" "name")))
 
(define flights-info (table-info "flights" (list "fid" "year" "month_id" "day_of_month" "day_of_week_id" "carrier_id" "flight_num" "origin_city" "origin_state" "dest_city" "dest_state" "departure_delay" "taxi_out" "arrival_delay" "canceled" "actual_time" "distance" "capacity" "price")))
 
(define-symbolic* str_san_francisco_ca_ integer?) 
(define-symbolic* str_seattle_wa_ integer?) 

(define (q1 tables) 
  (SELECT-DISTINCT (VALS "c.name") 
  FROM (JOIN (AS (NAMED (list-ref tables 3)) ["f"]) (AS (NAMED (list-ref tables 2)) ["c"])) 
  WHERE (AND (AND (BINOP "f.origin_city" = str_seattle_wa_) (BINOP "f.dest_city" = str_san_francisco_ca_)) (BINOP "f.carrier_id" = "c.cid"))))

(define (q2 tables) 
  (SELECT-DISTINCT (VALS "c.name") 
  FROM (AS (NAMED (list-ref tables 2)) ["c"]) 
  WHERE (EXISTS (AS (SELECT (VALS "f.fid" "f.year" "f.month_id" "f.day_of_month" "f.day_of_week_id" "f.carrier_id" "f.flight_num" "f.origin_city" "f.origin_state" "f.dest_city" "f.dest_state" "f.departure_delay" "f.taxi_out" "f.arrival_delay" "f.canceled" "f.actual_time" "f.distance" "f.capacity" "f.price") 
  FROM (AS (NAMED (list-ref tables 3)) ["f"]) 
  WHERE (AND (AND (BINOP "f.origin_city" = str_seattle_wa_) (BINOP "f.dest_city" = str_san_francisco_ca_)) (BINOP "f.carrier_id" = "c.cid"))) ["anyname" (list "fid" "year" "month_id" "day_of_month" "day_of_week_id" "carrier_id" "flight_num" "origin_city" "origin_state" "dest_city" "dest_state" "departure_delay" "taxi_out" "arrival_delay" "canceled" "actual_time" "distance" "capacity" "price")]))))


(define ros-instance (list q1 q2 (list months-info weekdays-info carriers-info flights-info))) 
