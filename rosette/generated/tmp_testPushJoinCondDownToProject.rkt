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
  (SELECT (VALS "dept.deptno" "emp.deptno") 
  FROM (JOIN (AS (NAMED (list-ref tables 3)) ["dept"]) (AS (NAMED (list-ref tables 4)) ["emp"])) 
  WHERE (BINOP (VAL-BINOP "dept.deptno" + 10) = (VAL-BINOP "emp.deptno" * 2))))

(define (q2 tables) 
  (SELECT (VALS "t1.deptno" "t2.deptno") 
  FROM (JOIN (AS (SELECT (VALS "dept0.deptno" "dept0.name" (VAL-BINOP "dept0.deptno" + 10)) 
  FROM (AS (NAMED (list-ref tables 3)) ["dept0"]) 
  WHERE (TRUE)) ["t1" (list "deptno" "name" "f2")]) (AS (SELECT (VALS "emp0.empno" "emp0.ename" "emp0.job" "emp0.mgr" "emp0.hiredate" "emp0.sal" "emp0.comm" "emp0.deptno" "emp0.slacker" (VAL-BINOP "emp0.deptno" * 2)) 
  FROM (AS (NAMED (list-ref tables 4)) ["emp0"]) 
  WHERE (TRUE)) ["t2" (list "empno" "ename" "job" "mgr" "hiredate" "sal" "comm" "deptno" "slacker" "f9")])) 
  WHERE (BINOP "t1.f2" = "t2.f9")))


(define ros-instance (list q1 q2 (list t-info account-info bonus-info dept-info emp-info))) 
