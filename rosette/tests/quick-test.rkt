#lang rosette 

(require "../cosette.rkt" "../sql.rkt" "../evaluator.rkt" "../syntax.rkt" 
         "../table.rkt" "../denotation.rkt" "../equal.rkt") 

(provide ros-instance)

(current-bitwidth #f)

(define emp-info (table-info "emp" (list "empno" "ename" "job" "mgr" "hiredate" "comm" "sal" "deptno" "slacker")))

(define (q1 tables) 
    (SELECT (VALS "emp.deptno" (VAL-BINOP "emp.deptno" + 1) (VAL-BINOP "emp.empno" + "emp.deptno")) 
        FROM (NAMED (RENAME (list-ref tables 0) "emp")) 
        WHERE (BINOP "emp.deptno" = 10)))

(define (q2 tables) 
    (SELECT (VALS 10 11 (VAL-BINOP "emp0.empno" + 10)) 
        FROM (NAMED (RENAME (list-ref tables 0) "emp0")) 
        WHERE (BINOP "emp0.deptno" = 10)))

(define ros-instance (list q1 q2 (list emp-info))) 

;;;;;;; test function

(define (test-now instance row-num)
    (let* ([table-info-list (list-ref instance 2)]
           [table-size-list (make-list (length table-info-list) row-num)]
           [tables (map (lambda (i) (gen-sym-table-from-info (list-ref table-info-list i)
                                                             (list-ref table-size-list i)))
                        (build-list (length table-info-list) values))]
           [q1 ((list-ref instance 0) tables)]
           [q2 ((list-ref instance 1) tables)])
      (cosette-solve q1 q2 tables)))

(test-now ros-instance 1)

(define t1
  (Table "emp" 
         (list "empno" "ename" "job" "mgr" "hiredate" "comm" "sal" "deptno" "slacker") 
         (list (cons (list 0 0 0 0 0 0 0 11 0) 0))))

(define qt1 (q1 (list t1)))
(define qt2 (q2 (list t1)))

(define r1 (denote-and-run qt1))
(define r2 (denote-and-run qt2))

(println r1)
(println r2)

(bag-equal (Table-content r1) 
           (Table-content r2))


