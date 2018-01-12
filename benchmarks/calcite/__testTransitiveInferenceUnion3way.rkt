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
  (SELECT (VALS 1) 
  FROM (JOIN (AS (UNION-ALL (SELECT (VALS "t3.deptno") 
  FROM (AS (UNION-ALL (SELECT (VALS "emp.deptno") 
  FROM (AS (NAMED (list-ref tables 4)) ["emp"]) 
  WHERE (BINOP "emp.deptno" > 7)) (SELECT (VALS "emp0.deptno") 
  FROM (AS (NAMED (list-ref tables 4)) ["emp0"]) 
  WHERE (BINOP "emp0.deptno" > 10))) ["t3" (list "deptno")]) 
  WHERE (TRUE)) (SELECT (VALS "emp1.deptno") 
  FROM (AS (NAMED (list-ref tables 4)) ["emp1"]) 
  WHERE (BINOP "emp1.deptno" > 1))) ["t6" (list "deptno")]) (AS (NAMED (list-ref tables 4)) ["emp2"])) 
  WHERE (BINOP "t6.deptno" = "emp2.deptno")))

(define (q2 tables) 
  (SELECT (VALS 1) 
  FROM (JOIN (AS (UNION-ALL (SELECT (VALS "t12.deptno") 
  FROM (AS (UNION-ALL (SELECT (VALS "emp3.deptno") 
  FROM (AS (NAMED (list-ref tables 4)) ["emp3"]) 
  WHERE (BINOP "emp3.deptno" > 7)) (SELECT (VALS "emp4.deptno") 
  FROM (AS (NAMED (list-ref tables 4)) ["emp4"]) 
  WHERE (BINOP "emp4.deptno" > 10))) ["t12" (list "deptno")]) 
  WHERE (TRUE)) (SELECT (VALS "emp5.deptno") 
  FROM (AS (NAMED (list-ref tables 4)) ["emp5"]) 
  WHERE (BINOP "emp5.deptno" > 1))) ["t15" (list "deptno")]) (AS (SELECT (VALS "emp6.empno" "emp6.ename" "emp6.job" "emp6.mgr" "emp6.hiredate" "emp6.comm" "emp6.sal" "emp6.deptno" "emp6.slacker") 
  FROM (AS (NAMED (list-ref tables 4)) ["emp6"]) 
  WHERE (OR (OR (BINOP "emp6.deptno" > 7) (BINOP "emp6.deptno" > 10)) (BINOP "emp6.deptno" > 1))) ["t16" (list "empno" "ename" "job" "mgr" "hiredate" "comm" "sal" "deptno" "slacker")])) 
  WHERE (BINOP "t15.deptno" = "t16.deptno")))


(define ros-instance (list q1 q2 (list t-info account-info bonus-info dept-info emp-info))) 
