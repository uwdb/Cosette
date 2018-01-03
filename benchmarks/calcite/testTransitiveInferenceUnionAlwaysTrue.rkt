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
  (SELECT (VALS "t0.deptno" "t4.deptno") 
  FROM (JOIN (AS (SELECT (VALS "emp.deptno") 
  FROM (NAMED (RENAME (list-ref tables 4) "emp")) 
  WHERE (BINOP "emp.deptno" < 4)) ["t0" (list "deptno")]) (AS (UNION-ALL (SELECT (VALS "emp0.deptno") 
  FROM (NAMED (RENAME (list-ref tables 4) "emp0")) 
  WHERE (BINOP "emp0.deptno" > 7)) (SELECT (VALS "emp1.deptno") 
  FROM (NAMED (RENAME (list-ref tables 4) "emp1")) 
  WHERE (TRUE))) ["t4" (list "deptno")])) 
  WHERE (BINOP "t0.deptno" = "t4.deptno")))

(define (q2 tables) 
  (SELECT (VALS "t6.deptno" "t11.deptno") 
  FROM (JOIN (AS (SELECT (VALS "emp2.deptno") 
  FROM (NAMED (RENAME (list-ref tables 4) "emp2")) 
  WHERE (BINOP "emp2.deptno" < 4)) ["t6" (list "deptno")]) (AS (SELECT (VALS "t10.deptno") 
  FROM (AS (UNION-ALL (SELECT (VALS "emp3.deptno") 
  FROM (NAMED (RENAME (list-ref tables 4) "emp3")) 
  WHERE (BINOP "emp3.deptno" > 7)) (SELECT (VALS "emp4.deptno") 
  FROM (NAMED (RENAME (list-ref tables 4) "emp4")) 
  WHERE (TRUE))) ["t10" (list "deptno")]) 
  WHERE (BINOP "t10.deptno" < 4)) ["t11" (list "deptno")])) 
  WHERE (BINOP "t6.deptno" = "t11.deptno")))


(define ros-instance (list q1 q2 (list t-info account-info bonus-info dept-info emp-info))) 
