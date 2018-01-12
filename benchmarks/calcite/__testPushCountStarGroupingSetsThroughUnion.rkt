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
  (SELECT (VALS "t.deptno" "t.job" (VAL-UNOP aggr-count (val-column-ref "t.empno"))) 
 FROM (AS (UNION-ALL (SELECT (VALS "emp.empno" "emp.ename" "emp.job" "emp.mgr" "emp.hiredate" "emp.comm" "emp.sal" "emp.deptno" "emp.slacker") 
  FROM (AS (NAMED (list-ref tables 4)) ["emp"]) 
  WHERE (TRUE)) (SELECT (VALS "emp0.empno" "emp0.ename" "emp0.job" "emp0.mgr" "emp0.hiredate" "emp0.comm" "emp0.sal" "emp0.deptno" "emp0.slacker") 
  FROM (AS (NAMED (list-ref tables 4)) ["emp0"]) 
  WHERE (TRUE))) ["t" (list "empno" "ename" "job" "mgr" "hiredate" "comm" "sal" "deptno" "slacker")]) 
 WHERE (TRUE) GROUP-BY (list "t.deptno" "t.job") 
 HAVING (TRUE)))

(define (q2 tables) 
  (SELECT (VALS "t6.deptno" "t6.job" (VAL-UNOP aggr-sum (VAL-UNOP aggr-count (val-column-ref "t6.deptno")))) 
 FROM (AS (UNION-ALL (SELECT (VALS "emp1.deptno" "emp1.job" (VAL-UNOP aggr-count (val-column-ref "emp1.empno"))) 
 FROM (AS (NAMED (list-ref tables 4)) ["emp1"]) 
 WHERE (TRUE) GROUP-BY (list "emp1.deptno" "emp1.job") 
 HAVING (TRUE)) (SELECT (VALS "emp2.deptno" "emp2.job" (VAL-UNOP aggr-count (val-column-ref "emp2.empno"))) 
 FROM (AS (NAMED (list-ref tables 4)) ["emp2"]) 
 WHERE (TRUE) GROUP-BY (list "emp2.deptno" "emp2.job") 
 HAVING (TRUE))) ["t6" (list "deptno" "job" "count_star")]) 
 WHERE (TRUE) GROUP-BY (list "t6.deptno" "t6.job") 
 HAVING (TRUE)))


(define ros-instance (list q1 q2 (list t-info account-info bonus-info dept-info emp-info))) 
