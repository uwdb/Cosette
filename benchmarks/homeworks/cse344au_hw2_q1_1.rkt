#lang rosette 
 
(require "../cosette.rkt" "../sql.rkt" "../evaluator.rkt" "../syntax.rkt") 
 
(provide ros-instance)
 
(current-bitwidth #f)
 
(define-symbolic div_ (~> integer? integer? integer?))
 
(define months-info (table-info "months" (list "mid" "month")))
 
(define weekdays-info (table-info "weekdays" (list "did" "day_of_week")))
 
(define carriers-info (table-info "carriers" (list "cid" "name")))
 
(define flights-info (table-info "flights" (list "fid" "year" "month_id" "day_of_month" "day_of_week_id" "carrier_id" "flight_num" "origin_city" "origin_state" "dest_city" "dest_state" "departure_delay" "taxi_out" "arrival_delay" "canceled" "actual_time" "distance" "capacity" "price")))
 
(define-symbolic* str_alaska_airlines_inc._ integer?) 
(define-symbolic* str_boston_ma_ integer?) 
(define-symbolic* str_seattle_wa_ integer?) 
(define-symbolic* str_monday_ integer?) 

(define (q1 tables) 
  (SELECT-DISTINCT (VALS "f.flight_num") 
  FROM (JOIN (NAMED (RENAME (list-ref tables 3) "f")) (JOIN (NAMED (RENAME (list-ref tables 2) "c")) (NAMED (RENAME (list-ref tables 1) "d")))) 
  WHERE (AND (AND (AND (AND (AND (BINOP "f.carrier_id" = "c.cid") (BINOP "f.day_of_week_id" = "d.did")) (BINOP "c.name" = str_alaska_airlines_inc._)) (BINOP "d.day_of_week" = str_monday_)) (BINOP "f.origin_city" = str_seattle_wa_)) (BINOP "f.dest_city" = str_boston_ma_))))

(define (q2 tables) 
  (SELECT-DISTINCT (VALS "f.flight_num") 
  FROM (JOIN (NAMED (RENAME (list-ref tables 3) "f")) (NAMED (RENAME (list-ref tables 2) "c"))) 
  WHERE (AND (AND (AND (BINOP "f.origin_city" = str_seattle_wa_) (BINOP "f.dest_city" = str_boston_ma_)) (BINOP "c.cid" = "f.carrier_id")) (BINOP "c.name" = str_alaska_airlines_inc._))))


(define ros-instance (list q1 q2 (list months-info weekdays-info carriers-info flights-info))) 
