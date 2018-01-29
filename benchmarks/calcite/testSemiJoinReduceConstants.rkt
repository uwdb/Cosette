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
  (SELECT (VALS "t0.sal") 
  FROM (JOIN (AS (SELECT (VALS "t.sal" "t.deptno") 
  FROM (AS (SELECT (VALS "emp.sal" "emp.deptno") 
  FROM (AS (NAMED (list-ref tables 4)) ["emp"]) 
  WHERE (TRUE)) ["t" (list "sal" "deptno")]) 
  WHERE (BINOP "t.deptno" = 200)) ["t0" (list "sal" "deptno")]) (AS (SELECT (VALS "t1.deptno") 
  FROM (AS (SELECT (VALS "emp0.sal" "emp0.deptno") 
  FROM (AS (NAMED (list-ref tables 4)) ["emp0"]) 
  WHERE (TRUE)) ["t1" (list "sal" "deptno")]) 
  WHERE (BINOP "t1.sal" = 100)) ["t3" (list "deptno")])) 
  WHERE (BINOP "t0.deptno" = "t3.deptno")))

(define (q2 tables) 
  (SELECT (VALS "t6.sal") 
  FROM (JOIN (AS (SELECT (VALS "t5.sal" "t5.deptno") 
  FROM (AS (SELECT (VALS "emp1.sal" "emp1.deptno") 
  FROM (AS (NAMED (list-ref tables 4)) ["emp1"]) 
  WHERE (TRUE)) ["t5" (list "sal" "deptno")]) 
  WHERE (BINOP "t5.deptno" = 200)) ["t6" (list "sal" "deptno")]) (AS (SELECT (VALS "t7.deptno") 
  FROM (AS (SELECT (VALS "emp2.sal" "emp2.deptno") 
  FROM (AS (NAMED (list-ref tables 4)) ["emp2"]) 
  WHERE (TRUE)) ["t7" (list "sal" "deptno")]) 
  WHERE (BINOP "t7.sal" = 100)) ["t9" (list "deptno")])) 
  WHERE (BINOP "t6.deptno" = "t9.deptno")))


(define ros-instance (list q1 q2 (list t-info account-info bonus-info dept-info emp-info))) 
