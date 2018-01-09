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
  (SELECT-DISTINCT (VALS "f.origin_city" "f.dest_city" "f.actual_time") 
  FROM (JOIN (NAMED (RENAME (list-ref tables 3) "f")) (AS (SELECT (VALS "a.origin_city" (VAL-UNOP aggr-max (val-column-ref "a.actual_time"))) 
 FROM (NAMED (RENAME (list-ref tables 3) "a")) 
 WHERE (TRUE) GROUP-BY (list "a.origin_city") 
 HAVING (TRUE)) ["x" (list "origin_city" "max_time")])) 
  WHERE (AND (BINOP "f.origin_city" = "x.origin_city") (BINOP "f.actual_time" = "x.max_time"))))

(define (q2 tables) 
  (SELECT (VALS "s.origin_city" "f2.dest_city" (VAL-UNOP aggr-max (val-column-ref "f2.actual_time"))) 
 FROM (JOIN (AS (SELECT (VALS "f1.origin_city" (VAL-UNOP aggr-max (val-column-ref "f1.actual_time"))) 
 FROM (NAMED (RENAME (list-ref tables 3) "f1")) 
 WHERE (TRUE) GROUP-BY (list "f1.origin_city") 
 HAVING (TRUE)) ["s" (list "origin_city" "max_time")]) (NAMED (RENAME (list-ref tables 3) "f2"))) 
 WHERE (AND (BINOP "s.origin_city" = "f2.origin_city") (BINOP "f2.actual_time" = "s.max_time")) GROUP-BY (list "s.origin_city" "f2.dest_city") 
 HAVING (TRUE)))


(define ros-instance (list q1 q2 (list months-info weekdays-info carriers-info flights-info))) 
