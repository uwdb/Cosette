#lang rosette 
 
(require "../denotation.rkt" "../cosette.rkt" "../sql.rkt" "../evaluator.rkt" "../syntax.rkt" "../symmetry.rkt") 
  
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
  (SELECT-DISTINCT (VALS "q.city") 
  FROM (AS (SELECT (VALS "f.origin_city" (VAL-UNOP aggr-max (val-column-ref "f.actual_time"))) 
 FROM (AS (NAMED (list-ref tables 3)) ["f"]) 
 WHERE (TRUE) GROUP-BY (list "f.origin_city") 
 HAVING (TRUE)) ["q" (list "city" "max_time")]) 
  WHERE (BINOP "q.max_time" < 180)))


(define table-info-list (list months-info weekdays-info carriers-info flights-info))
(define table-size-list (make-list (length table-info-list) 1))
(define tables (map (lambda (i) (gen-sym-table-from-info (list-ref table-info-list i)
                                                         (list-ref table-size-list i)))
                    (build-list (length table-info-list) values)))

(define qt1 (q1 tables))
(define qt2 (q2 tables))

(define c1 (big-step (init-constraint qt1) 20))
(define c2 (big-step (init-constraint qt2) 20))

;(displayln (to-str (constr-flatten c1)))
;(displayln (to-str (constr-flatten c2)))


(displayln (to-str (go-break-symmetry-bounded qt1 qt2)))

