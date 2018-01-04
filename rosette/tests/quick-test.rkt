#lang rosette 

(require "../cosette.rkt" "../sql.rkt" "../evaluator.rkt" "../syntax.rkt" 
         "../table.rkt" "../denotation.rkt" "../equal.rkt" "../util.rkt") 

(provide ros-instance)

(current-bitwidth #f)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
 (define-symbolic div_ (~> integer? integer? integer?))
 
(define flights-info (table-info "flights" (list "fid" "year" "month_id" "day_of_month" "day_of_week_id" "carrier_id" "flight_num" "origin_city" "origin_state" "dest_city" "dest_state" "departure_delay" "taxi_out" "arrival_delay" "canceled" "actual_time" "distance" "capacity" "price")))
 

(define (q1 tables) 
  (SELECT (VALS "f1.origin_city" "f1.dest_city" "f1.actual_time") 
 FROM (JOIN (NAMED (RENAME (list-ref tables 0) "f1")) 
            (NAMED (RENAME (list-ref tables 0) "f2")))
 WHERE (BINOP "f1.origin_city" = "f2.origin_city") 
 GROUP-BY (list "f1.origin_city" "f1.dest_city" "f1.actual_time") 
 HAVING (TRUE)))

(define (q2 tables) 
  (SELECT (VALS "f1.origin_city" "f1.dest_city" "f1.actual_time") 
 FROM (JOIN (NAMED (RENAME (list-ref tables 0) "f1")) 
            (NAMED (RENAME (list-ref tables 0) "f2")))
 WHERE (BINOP "f1.origin_city" = "f2.origin_city") 
 GROUP-BY (list "f1.origin_city" "f1.dest_city" "f1.actual_time") 
 HAVING  (BINOP "f1.actual_time" = (VAL-UNOP aggr-max (val-column-ref "f2.actual_time")))))


(define ros-instance (list q1 q2 (list flights-info))) 
;;;;;;; test function

(define (test-now instance row-num)
    (let* ([table-info-list (list-ref instance 2)]
           [table-size-list (make-list (length table-info-list) row-num)]
           [tables (map (lambda (i) (gen-sym-table-from-info (list-ref table-info-list i)
                                                             (list-ref table-size-list i)))
                        (build-list (length table-info-list) values))]
           [q1 ((list-ref instance 0) tables)]
           [q2 ((list-ref instance 1) tables)])
      (println "=======================")
      (verify (same q1 q2))
      (println "0000000000000000000000")
      (cosette-solve q1 q2 tables)))

(test-now ros-instance 2)

;(exit)

(define t1
  (Table "flights" (list "fid" "year" "month_id" "day_of_month" "day_of_week_id" "carrier_id" "flight_num" "origin_city" "origin_state" "dest_city" "dest_state" "departure_delay" "taxi_out" "arrival_delay" "canceled" "actual_time" "distance" "capacity" "price")
         (list (cons (list 0 1 2 3 4 5 6 7 8 9 10 11 12 13 14 15 16 17 18) 1)
               (cons (list 1 3 5 3 46 5 6 71 8 9 10 11 12 13 14 15 16 17 11) 1))))

;(define t2
;  (Table "emp" 
;         (list "empno" "ename" "job" "mgr" "hiredate" "comm" "sal" "deptno" "slacker")
;         (list (cons (list 0 0 0 0 0 0 0 0 0) 2))))

(define qt1 (q1 (list t1)))
(define qt2 (q2 (list t1)))

(define r1 (denote-and-run qt1))
(define r2 (denote-and-run qt2))

(println r1)
(println r2)

;(bag-equal (Table-content r1) 
;           (Table-content r2))


