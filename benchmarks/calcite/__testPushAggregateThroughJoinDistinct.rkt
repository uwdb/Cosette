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
  (SELECT (VALS "t.name" (VAL-UNOP aggr-sum (val-column-ref "emp.sal")) (VAL-UNOP aggr-count (val-column-ref "t.name"))) 
 FROM (JOIN (NAMED (RENAME (list-ref tables 4) "emp")) (AS (SELECT (VALS "dept.name") 
 FROM (NAMED (RENAME (list-ref tables 3) "dept")) 
 WHERE (TRUE) GROUP-BY (list "dept.name") 
 HAVING (TRUE)) ["t" (list "name")])) 
 WHERE (BINOP "emp.job" = "t.name") GROUP-BY (list "t.name") 
 HAVING (TRUE)))

(define (q2 tables) 
  (SELECT (VALS "t2.name" "t1.sum_sal" "t1.c") 
  FROM (JOIN (AS (SELECT (VALS "emp0.job" (VAL-UNOP aggr-sum (val-column-ref "emp0.sal")) (VAL-UNOP aggr-count (val-column-ref "emp0.empno"))) 
 FROM (NAMED (RENAME (list-ref tables 4) "emp0")) 
 WHERE (TRUE) GROUP-BY (list "emp0.job") 
 HAVING (TRUE)) ["t1" (list "job" "sum_sal" "c")]) (AS (SELECT (VALS "dept0.name") 
 FROM (NAMED (RENAME (list-ref tables 3) "dept0")) 
 WHERE (TRUE) GROUP-BY (list "dept0.name") 
 HAVING (TRUE)) ["t2" (list "name")])) 
  WHERE (BINOP "t1.job" = "t2.name")))


(define ros-instance (list q1 q2 (list t-info account-info bonus-info dept-info emp-info))) 
