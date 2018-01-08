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
  (SELECT (VALS "t.job" "dept.name") 
 FROM (JOIN (AS (SELECT (VALS "emp.empno" "emp.ename" "emp.job" "emp.mgr" "emp.hiredate" "emp.comm" "emp.sal" "emp.deptno" "emp.slacker") 
  FROM (NAMED (RENAME (list-ref tables 4) "emp")) 
  WHERE (BINOP "emp.empno" = 10)) ["t" (list "empno" "ename" "job" "mgr" "hiredate" "comm" "sal" "deptno" "slacker")]) (NAMED (RENAME (list-ref tables 3) "dept"))) 
 WHERE (BINOP "t.job" = "dept.name") GROUP-BY (list "t.job" "dept.name") 
 HAVING (TRUE)))

(define (q2 tables) 
  (SELECT (VALS "t2.job" "t3.name") 
  FROM (JOIN (AS (SELECT (VALS "emp0.job") 
 FROM (NAMED (RENAME (list-ref tables 4) "emp0")) 
 WHERE (BINOP "emp0.empno" = 10) GROUP-BY (list "emp0.job") 
 HAVING (TRUE)) ["t2" (list "job")]) (AS (SELECT (VALS "dept0.name") 
 FROM (NAMED (RENAME (list-ref tables 3) "dept0")) 
 WHERE (TRUE) GROUP-BY (list "dept0.name") 
 HAVING (TRUE)) ["t3" (list "name")])) 
  WHERE (BINOP "t2.job" = "t3.name")))


(define ros-instance (list q1 q2 (list t-info account-info bonus-info dept-info emp-info))) 
