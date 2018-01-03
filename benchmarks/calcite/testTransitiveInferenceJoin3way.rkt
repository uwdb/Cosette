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
  FROM (JOIN (AS (SELECT (VALS "emp.empno" "emp.ename" "emp.job" "emp.mgr" "emp.hiredate" "emp.comm" "emp.sal" "emp.deptno" "emp.slacker") 
  FROM (NAMED (RENAME (list-ref tables 4) "emp")) 
  WHERE (BINOP "emp.deptno" > 7)) ["t" (list "empno" "ename" "job" "mgr" "hiredate" "comm" "sal" "deptno" "slacker")]) (JOIN (NAMED (RENAME (list-ref tables 4) "emp0")) (NAMED (RENAME (list-ref tables 4) "emp1")))) 
  WHERE (AND (BINOP "t.deptno" = "emp0.deptno") (BINOP "emp0.deptno" = "emp1.deptno"))))

(define (q2 tables) 
  (SELECT (VALS 1) 
  FROM (JOIN (AS (SELECT (VALS "emp2.empno" "emp2.ename" "emp2.job" "emp2.mgr" "emp2.hiredate" "emp2.comm" "emp2.sal" "emp2.deptno" "emp2.slacker") 
  FROM (NAMED (RENAME (list-ref tables 4) "emp2")) 
  WHERE (BINOP "emp2.deptno" > 7)) ["t1" (list "empno" "ename" "job" "mgr" "hiredate" "comm" "sal" "deptno" "slacker")]) (JOIN (AS (SELECT (VALS "emp3.empno" "emp3.ename" "emp3.job" "emp3.mgr" "emp3.hiredate" "emp3.comm" "emp3.sal" "emp3.deptno" "emp3.slacker") 
  FROM (NAMED (RENAME (list-ref tables 4) "emp3")) 
  WHERE (BINOP "emp3.deptno" > 7)) ["t2" (list "empno" "ename" "job" "mgr" "hiredate" "comm" "sal" "deptno" "slacker")]) (AS (SELECT (VALS "emp4.empno" "emp4.ename" "emp4.job" "emp4.mgr" "emp4.hiredate" "emp4.comm" "emp4.sal" "emp4.deptno" "emp4.slacker") 
  FROM (NAMED (RENAME (list-ref tables 4) "emp4")) 
  WHERE (BINOP "emp4.deptno" > 7)) ["t3" (list "empno" "ename" "job" "mgr" "hiredate" "comm" "sal" "deptno" "slacker")]))) 
  WHERE (AND (BINOP "t1.deptno" = "t2.deptno") (BINOP "t2.deptno" = "t3.deptno"))))


(define ros-instance (list q1 q2 (list t-info account-info bonus-info dept-info emp-info))) 
