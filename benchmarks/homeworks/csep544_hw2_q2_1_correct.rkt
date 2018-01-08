#lang rosette 
 
(require "../cosette.rkt" "../sql.rkt" "../evaluator.rkt" "../syntax.rkt") 
 
(provide ros-instance)
 
(current-bitwidth #f)
 
(define-symbolic div_ (~> integer? integer? integer?))
 
(define months-info (table-info "months" (list "mid" "month")))
 
(define weekdays-info (table-info "weekdays" (list "did" "day_of_week")))
 
(define carriers-info (table-info "carriers" (list "cid" "name")))
 
(define flights-info (table-info "flights" (list "fid" "year" "month_id" "day_of_month" "day_of_week_id" "carrier_id" "flight_num" "origin_city" "origin_state" "dest_city" "dest_state" "departure_delay" "taxi_out" "arrival_delay" "canceled" "actual_time" "distance" "capacity" "price")))
 
(define-symbolic* str_boston_ma_ integer?) 
(define-symbolic* str_seattle_wa_ integer?) 
(define-symbolic* str_july_ integer?) 

(define (q1 tables) 
  (SELECT (VALS "c.name" "f1.fid" "f1.origin_city" "f1.dest_city" "f1.actual_time" "f2.fid" "f2.origin_city" "f2.dest_city" "f2.actual_time" (VAL-BINOP "f1.actual_time" + "f2.actual_time")) 
  FROM (JOIN (NAMED (RENAME (list-ref tables 3) "f1")) (JOIN (NAMED (RENAME (list-ref tables 3) "f2")) (JOIN (NAMED (RENAME (list-ref tables 0) "m")) (NAMED (RENAME (list-ref tables 2) "c"))))) 
  WHERE (AND (AND (AND (AND (AND (AND (AND (AND (AND (AND (AND (AND (BINOP "f1.month_id" = "m.mid") (BINOP "f1.carrier_id" = "c.cid")) (BINOP "f1.month_id" = "f2.month_id")) (BINOP "f1.day_of_month" = "f2.day_of_month")) (BINOP "f1.year" = "f2.year")) (BINOP "f1.carrier_id" = "f2.carrier_id")) (BINOP "m.month" = str_july_)) (BINOP "f1.day_of_month" = 15)) (BINOP "f1.year" = 2015)) (BINOP "f1.dest_city" = "f2.origin_city")) (BINOP "f1.origin_city" = str_seattle_wa_)) (BINOP "f2.dest_city" = str_boston_ma_)) (BINOP (VAL-BINOP "f1.actual_time" + "f2.actual_time") < 420))))

(define (q2 tables) 
  (SELECT (VALS "c.name" "f1.flight_num" "f1.origin_city" "f1.dest_city" "f1.actual_time" "f2.flight_num" "f2.origin_city" "f2.dest_city" "f2.actual_time" (VAL-BINOP "f1.actual_time" + "f2.actual_time")) 
  FROM (JOIN (NAMED (RENAME (list-ref tables 3) "f1")) (JOIN (NAMED (RENAME (list-ref tables 3) "f2")) (JOIN (NAMED (RENAME (list-ref tables 0) "m")) (NAMED (RENAME (list-ref tables 2) "c"))))) 
  WHERE (AND (AND (AND (AND (AND (AND (BINOP "f1.carrier_id" = "c.cid") (BINOP "f2.carrier_id" = "c.cid")) (BINOP "f1.month_id" = "m.mid")) (BINOP "f2.month_id" = "m.mid")) (BINOP "f1.carrier_id" = "f2.carrier_id")) (BINOP "f1.dest_city" = "f2.origin_city")) (AND (AND (AND (AND (AND (AND (AND (BINOP "m.month" = str_july_) (BINOP "f1.day_of_month" = 15)) (BINOP "f2.day_of_month" = 15)) (BINOP "f1.year" = 2015)) (BINOP "f2.year" = 2015)) (BINOP "f1.origin_city" = str_seattle_wa_)) (BINOP "f2.dest_city" = str_boston_ma_)) (BINOP (VAL-BINOP "f1.actual_time" + "f2.actual_time") < 420)))))


(define ros-instance (list q1 q2 (list months-info weekdays-info carriers-info flights-info))) 
