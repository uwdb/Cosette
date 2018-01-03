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
  WHERE (AND (AND (BINOP "emp.deptno" > 7) (BINOP "emp.comm" = "emp.deptno")) (BINOP (VAL-BINOP "emp.comm" + "emp.deptno") > (VAL-BINOP "emp.comm" div_ 2)))) ["t" (list "empno" "ename" "job" "mgr" "hiredate" "comm" "sal" "deptno" "slacker")]) (AS (SELECT (VALS "emp0.empno" "emp0.ename" "emp0.job" "emp0.mgr" "emp0.hiredate" "emp0.comm" "emp0.sal" "emp0.deptno" "emp0.slacker") 
  FROM (NAMED (RENAME (list-ref tables 4) "emp0")) 
  WHERE (BINOP "emp0.sal" = "emp0.deptno")) ["t0" (list "empno" "ename" "job" "mgr" "hiredate" "comm" "sal" "deptno" "slacker")])) 
  WHERE (BINOP "t.deptno" = "t0.deptno")))

(define (q2 tables) 
  (SELECT (VALS 1) 
  FROM (JOIN (AS (SELECT (VALS "emp1.empno" "emp1.ename" "emp1.job" "emp1.mgr" "emp1.hiredate" "emp1.comm" "emp1.sal" "emp1.deptno" "emp1.slacker") 
  FROM (NAMED (RENAME (list-ref tables 4) "emp1")) 
  WHERE (AND (AND (BINOP "emp1.deptno" > 7) (BINOP "emp1.comm" = "emp1.deptno")) (BINOP (VAL-BINOP "emp1.comm" + "emp1.deptno") > (VAL-BINOP "emp1.comm" div_ 2)))) ["t2" (list "empno" "ename" "job" "mgr" "hiredate" "comm" "sal" "deptno" "slacker")]) (AS (SELECT (VALS "t3.empno" "t3.ename" "t3.job" "t3.mgr" "t3.hiredate" "t3.comm" "t3.sal" "t3.deptno" "t3.slacker") 
  FROM (AS (SELECT (VALS "emp2.empno" "emp2.ename" "emp2.job" "emp2.mgr" "emp2.hiredate" "emp2.comm" "emp2.sal" "emp2.deptno" "emp2.slacker") 
  FROM (NAMED (RENAME (list-ref tables 4) "emp2")) 
  WHERE (BINOP "emp2.sal" = "emp2.deptno")) ["t3" (list "empno" "ename" "job" "mgr" "hiredate" "comm" "sal" "deptno" "slacker")]) 
  WHERE (BINOP "t3.deptno" > 7)) ["t4" (list "empno" "ename" "job" "mgr" "hiredate" "comm" "sal" "deptno" "slacker")])) 
  WHERE (BINOP "t2.deptno" = "t4.deptno")))


(define ros-instance (list q1 q2 (list t-info account-info bonus-info dept-info emp-info))) 
