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
  FROM (JOIN (AS (NAMED (list-ref tables 2)) ["c"]) (AS (SELECT (VALS "f2.carrier_id" "f2.dest_city") 
  FROM (AS (NAMED (list-ref tables 3)) ["f2"]) 
  WHERE (BINOP "f2.origin_city" = str_seattle_wa_)) ["f" (list "carrier_id" "dest_city")])) 
  WHERE (AND (BINOP "c.cid" = "f.carrier_id") (BINOP "f.dest_city" = str_san_francisco_ca_))))


(define ros-instance (list q1 q2 (list months-info weekdays-info carriers-info flights-info))) 
