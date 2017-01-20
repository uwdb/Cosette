#lang rosette                                                                                                                                                 

(require "../util.rkt" "../table.rkt" "../sql.rkt" "../evaluator.rkt" "../equal.rkt")

(define acontent
    (list
      (cons (list 1 0 1) 8)))

(define sEmp (Table "Emp" (list "Name" "Emp" "Dept") (gen-sym-schema 3 2)))    
(define sDept (Table "Dept" (list "Dept" "Mgr" "Loc") (gen-sym-schema 3 2)))    

(define Emp (Table "Emp" (list "Name" "Emp" "Dept") acontent))    
(define Dept (Table "Dept" (list "Dept" "Mgr" "Loc") acontent))    
	    
(define subq (SELECT (VALS "Dept.Dept")
	FROM (NAMED sDept)
	WHERE (AND (AND (BINOP 0 eq? "Dept.Mgr") (BINOP 1 eq? "Dept.Dept")) (BINOP "Dept.Loc" eq? 1))))

;; (run subq)

(define q1
  (SELECT (VALS "Emp.Name")
     FROM (NAMED sEmp)
    WHERE (EXISTS 
	    (SELECT (VALS "Dept.Dept")
	       FROM (NAMED sDept)
	      WHERE (AND (AND (BINOP "Emp.Emp" eq? "Dept.Mgr") (BINOP "Emp.Dept" eq? "Dept.Dept")) (BINOP "Dept.Loc" eq? 1))))))

(define q2
  (SELECT (VALS "Emp.Name")
     FROM (JOIN (NAMED sEmp) (NAMED sDept))
    WHERE (AND (BINOP "Emp.Dept" eq? "Dept.Dept") (AND (BINOP "Dept.Loc" eq? 1) (BINOP "Emp.Emp" eq? "Dept.Mgr")))))

;; (run q1)
;; (run q2)

;; model expected
(time (verify (same q1 q2)))
