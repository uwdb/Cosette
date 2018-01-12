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
  (SELECT (VALS "t1.ename" (VAL-UNOP aggr-sum (val-column-ref "t1.u"))) 
 FROM (AS (UNION-ALL (SELECT (VALS "emp.empno" "emp.ename" "emp.job" "emp.mgr" "emp.hiredate" "emp.sal" "emp.comm" "emp.deptno" "emp.slacker" 2) 
  FROM (AS (NAMED (list-ref tables 4)) ["emp"]) 
  WHERE (TRUE)) (SELECT (VALS "emp0.empno" "emp0.ename" "emp0.job" "emp0.mgr" "emp0.hiredate" "emp0.sal" "emp0.comm" "emp0.deptno" "emp0.slacker" 3) 
  FROM (AS (NAMED (list-ref tables 4)) ["emp0"]) 
  WHERE (TRUE))) ["t1" (list "empno" "ename" "job" "mgr" "hiredate" "sal" "comm" "deptno" "slacker" "u")]) 
 WHERE (TRUE) GROUP-BY (list "t1.ename") 
 HAVING (TRUE)))

(define (q2 tables) 
  (SELECT (VALS "t8.ename" (VAL-UNOP aggr-sum (VAL-UNOP aggr-sum 3))) 
 FROM (AS (UNION-ALL (SELECT (VALS "emp1.ename" (VAL-UNOP aggr-sum 2)) 
 FROM (AS (NAMED (list-ref tables 4)) ["emp1"]) 
 WHERE (TRUE) GROUP-BY (list "emp1.ename") 
 HAVING (TRUE)) (SELECT (VALS "emp2.ename" (VAL-UNOP aggr-sum 3)) 
 FROM (AS (NAMED (list-ref tables 4)) ["emp2"]) 
 WHERE (TRUE) GROUP-BY (list "emp2.ename") 
 HAVING (TRUE))) ["t8" (list "ename" "sum_num2")]) 
 WHERE (TRUE) GROUP-BY (list "t8.ename") 
 HAVING (TRUE)))


(define ros-instance (list q1 q2 (list t-info account-info bonus-info dept-info emp-info))) 
