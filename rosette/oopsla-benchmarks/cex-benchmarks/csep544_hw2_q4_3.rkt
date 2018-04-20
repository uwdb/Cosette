#lang rosette 
 
(require "../cosette.rkt" "../sql.rkt" "../evaluator.rkt" "../syntax.rkt") 
 
(provide ros-instance)
 
(current-bitwidth #f)
 
(define-symbolic div_ (~> integer? integer? integer?))
 
(define months-info (table-info "months" (list "mid" "month")))
 
(define weekdays-info (table-info "weekdays" (list "did" "day_of_week")))
 
(define carriers-info (table-info "carriers" (list "cid" "name")))
 
(define flights-info (table-info "flights" (list "fid" "year" "month_id" "day_of_month" "carrier_id")))
 

(define (q1 tables) 
  (SELECT (VALS "c.name") 
 FROM (JOIN (AS (NAMED (list-ref tables 2)) ["c"]) (AS (NAMED (list-ref tables 3)) ["f"])) 
 WHERE (BINOP "c.cid" = "f.carrier_id") GROUP-BY (list "c.cid" "c.name" "f.year" "f.month_id" "f.day_of_month") 
 HAVING (BINOP (VAL-UNOP aggr-count (val-column-ref "f.fid")) > 1000)))

(define (q2 tables) 
  (SELECT (VALS "c.name") 
 FROM (JOIN (AS (NAMED (list-ref tables 3)) ["f"]) (AS (NAMED (list-ref tables 2)) ["c"])) 
 WHERE (BINOP "f.carrier_id" = "c.cid") GROUP-BY (list "f.day_of_month" "c.name") 
 HAVING (BINOP (VAL-UNOP aggr-count (val-column-ref "f.fid")) > 1000)))


(define ros-instance (list q1 q2 (list months-info weekdays-info carriers-info flights-info))) 
