#lang rosette

(provide (all-defined-out))
;(provide tuple-in table-sum bag-contain bag-equal)

; sum the multiplicity of tuples in a table
(define (sum table)
  (cond
    [(empty? table) 0]
    [else (+ (cdr (first table)) (sum (rest table)))]))

;filter same tuple
(define (filter-tuple t table)
  (filter
    (lambda (t1) (equal? (car t) (car t1)))
     table))

; remove tuple with multiplicity 0
(define (remove-zero table)
  (filter (lambda (t) (not (eq? (cdr t) 0))) table))

; sum the multiplicity of each tuple in a table
; eg (list ((1, 1, 2), 2) ((1, 1, 2), 2)) will become (list ((1, 1, 2), 4) ((1, 1, 2), 4))
(define (table-sum table)
  (map (lambda (t)
        (cons (car t) (sum (filter-tuple t table))))
        (remove-zero table))
  )

; check the containment of element in a list
(define (element-contain t l)
  (cond
    [(empty? l) #f]
    [else (or (equal? t (first l)) (element-contain t (rest l)))]))

; check the set containment of two list, if l1 is contained in l2, return true
(define (contain l1 l2)
  (cond
    [(empty? l1) #t]
    [else (and (element-contain (first l1) l2) (contain (rest l1) l2))]
))

(define (contain-fueled l1 l2 fuel)
  (cond
    [(<= fuel 0) #f]
    [(empty? l1) #t]
    [else (and (element-contain (first l1) l2) (contain-fueled (rest l1) l2 (- fuel 1)))]
))

; bag equal definition
(define (bag-equal table1 table2)
  (let ([l1 (table-sum table1)])
    (let ([l2 (table-sum table2)])
      (and (contain l1 l2) (contain l2 l1)))))
 
