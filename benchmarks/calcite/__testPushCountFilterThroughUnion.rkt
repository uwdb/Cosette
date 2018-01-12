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
  (SELECT (VALS "t1.deptno" (VAL-UNOP aggr-count (val-column-ref "t1.empno"))) 
 FROM (AS (UNION-ALL (SELECT (VALS "emp.empno" "emp.ename" "emp.job" "emp.mgr" "emp.hiredate" "emp.comm" "emp.sal" "emp.deptno" "emp.slacker") 
  FROM (AS (NAMED (list-ref tables 4)) ["emp"]) 
  WHERE (BINOP "emp.deptno" = 10)) (SELECT (VALS "emp0.empno" "emp0.ename" "emp0.job" "emp0.mgr" "emp0.hiredate" "emp0.comm" "emp0.sal" "emp0.deptno" "emp0.slacker") 
  FROM (AS (NAMED (list-ref tables 4)) ["emp0"]) 
  WHERE (BINOP "emp0.deptno" > 20))) ["t1" (list "empno" "ename" "job" "mgr" "hiredate" "comm" "sal" "deptno" "slacker")]) 
 WHERE (TRUE) GROUP-BY (list "t1.deptno") 
 HAVING (TRUE)))

(define (q2 tables) 
  (SELECT (VALS "t10.deptno" (VAL-UNOP aggr-sum (VAL-UNOP aggr-count (val-column-ref "t10.deptno")))) 
 FROM (AS (UNION-ALL (SELECT (VALS "emp1.deptno" (VAL-UNOP aggr-count (val-column-ref "emp1.empno"))) 
 FROM (AS (NAMED (list-ref tables 4)) ["emp1"]) 
 WHERE (BINOP "emp1.deptno" = 10) GROUP-BY (list "emp1.deptno") 
 HAVING (TRUE)) (SELECT (VALS "emp2.deptno" (VAL-UNOP aggr-count (val-column-ref "emp2.empno"))) 
 FROM (AS (NAMED (list-ref tables 4)) ["emp2"]) 
 WHERE (BINOP "emp2.deptno" > 20) GROUP-BY (list "emp2.deptno") 
 HAVING (TRUE))) ["t10" (list "deptno" "count_star")]) 
 WHERE (TRUE) GROUP-BY (list "t10.deptno") 
 HAVING (TRUE)))


(define ros-instance (list q1 q2 (list t-info account-info bonus-info dept-info emp-info))) 
