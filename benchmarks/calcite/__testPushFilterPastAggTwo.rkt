#lang rosette 
 
(require "../cosette.rkt" "../sql.rkt" "../evaluator.rkt" "../syntax.rkt") 
 
(provide ros-instance)
 
(current-bitwidth #f)
 
(define-symbolic div_ (~> integer? integer? integer?))
 
(define t-info (table-info "t" (list "k0" "c1" "f1_a0" "f2_a0" "f0_c0" "f1_c0" "f0_c1" "f1_c2" "f2_c3")))
 
(define account-info (table-info "account" (list "acctno" "type" "balance")))
 
(define bonus-info (table-info "bonus" (list "ename" "job" "sal" "comm")))
 
(define dept-info (table-info "dept" (list "deptno" "name")))
 
(define emp-info (table-info "emp" (list "empno" "ename" "job" "mgr" "hiredate" "comm" "sal" "deptno" "slacker")))
 

(define (q1 tables) 
  (SELECT (VALS "dept.name") 
 FROM (NAMED (RENAME (list-ref tables 3) "dept")) 
 WHERE (BINOP "dept.name" > 1) GROUP-BY (list "dept.name") 
 HAVING (AND (BINOP "dept.name" > 2) (OR (BINOP (VAL-UNOP aggr-count (val-column-ref "dept.deptno")) > 30) (BINOP "dept.name" < 3)))))

(define (q2 tables) 
  (SELECT (VALS "t6.c1") 
 FROM (AS (SELECT (VALS "dept0.name") 
  FROM (NAMED (RENAME (list-ref tables 3) "dept0")) 
  WHERE (BINOP "dept0.name" > 1)) ["t6" (list "c1")]) 
 WHERE (BINOP "t6.c1" > 2) GROUP-BY (list "t6.c1") 
 HAVING (OR (BINOP (VAL-UNOP aggr-count (val-column-ref "t6.c1")) > 30) (BINOP "t6.c1" < 3))))


(define ros-instance (list q1 q2 (list t-info account-info bonus-info dept-info emp-info))) 
