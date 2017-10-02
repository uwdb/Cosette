#lang rosette

(require "table.rkt")

(provide dedup
         dedup-accum
         projection
         cross-prod
         get-row-count
         equi-join
         left-outer-join
         left-outer-join-2
         left-outer-join-raw
         table-content-empty?
         table-content-ascending?
         list-distinct?
         table-diff
         union-all
         extend-each-row
         xproduct
         xproduct-raw
         sqlnull
         aggr-raw
         group-by-raw
         transpose)

(define sqlnull "sqlnull")

;; rawTable -> rawTable -> rawTable
(define (xproduct-raw a b)
  (let ([imr (cartes-prod a b)])
    (map 
      (lambda (x)
        (cons 
          (append (car (car x)) 
                  (car (second x))) 
          (* (cdr (car x)) 
             (cdr (second x))))) 
      imr)))

(define (cartes-prod a b)
  (let ([one-v-many (lambda (x)
                      (map (lambda (e) (list x e)) b))])
    (foldr append '() (map one-v-many a))))

;; Table -> Table -> Table
(define (xproduct a b name)
  (Table name (schema-join a b) (xproduct-raw (Table-content a) (Table-content b))))

;; given a table (content only), judge whether the table is empty
(define (table-content-empty? table)
  (foldl && #t (map (lambda (r) (zero? (cdr r))) table)))

(define (table-content-ascending? table)
  (cond
    [(equal? table '()) #t]
    [(equal? (cdr table) '()) #t]
    [(equal? (dict-order-compare (car (car table)) 
                                 (car (car (cdr table)))) 
             -1) (table-content-ascending? (cdr table))]
    [else #f]))

; given two lists with the same length, 
; judge their partial order under dict order
; 0 : l1 == l2
; -1 : l1 < l2
; 1 : l1 > l2
(define (dict-order-compare l1 l2)
  (cond
    [(and (equal? '() l1) (equal? '() l2)) 0]
    [(> (car l1) (car l2)) 1]
    [(< (car l1) (car l2)) -1]
    [else (dict-order-compare (cdr l1) (cdr l2))]))

; perform aggregation on a table :table
; Arguments:
;     table: the table to be aggregated, which contains only table-content but not schema
;     aggr-field-indices: indices of the fields to be aggregated, reprented in a list
;     raw-aggr-fun: the aggregation function to be used; it takes in a list of pairs [(v1 . mul1), ..., (vn . muln)] and
;                returns a single aggregation value
;     target-index: the target field to be used in aggregation
(define (aggr-raw table aggr-field-indices raw-aggr-fun target-index)
  (cond 
    [(equal? '() table) '()]
    [else 
      (let* ([row (car table)]
             [aggr-key-vals (map (lambda (i) (list-ref (car row) i)) aggr-field-indices)]
             [target-val (list-ref (car row) target-index)])
        (cons
          (let ([same-val-rows 
                  (map (lambda (r) (cons (list-ref (car r) target-index) (cdr r)))
                       (filter (lambda (r) (equal? aggr-key-vals
                                                   (map (lambda (i) (list-ref (car r) i))
                                                        aggr-field-indices)))
                               table))])
            (cons (append aggr-key-vals (list (raw-aggr-fun same-val-rows))) 
                  (if (table-content-empty? same-val-rows) 0 1)))
          (aggr-raw (filter (lambda (r) (not (equal? aggr-key-vals
                                                     (map (lambda (i) (list-ref (car r) i))
                                                          aggr-field-indices))))
                            (cdr table))
                    aggr-field-indices
                    raw-aggr-fun
                    target-index)))]))

; perform aggregation on a table :table, result as follows:
;   we segment a table into a list of tables and each table is the result of a group
; each cell contain a list of tuples, specifying each value appear in the group and the number of times it appears
; Arguments:
;     table: the table to be aggregated, which contains only table-content but not schema
;     group-by-indices: indices of the fields to be aggregated, reprented in a list
;     target-indice: the target fields to be used in aggregation 
;                    (we only collect them without actually perform any aggregation)
(define (group-by-raw table group-by-indices)
  (cond 
    [(equal? '() table) '()]
    [else 
      (let* ([row (car table)]
             [target-indices (range (length (car row)))]
             [gb-key-vals (map (lambda (i) (list-ref (car row) i)) group-by-indices)])
        (cons
          (let* ([same-val-rows 
                   (map (lambda (r) 
                          (cons (map (lambda (idx) (cons (list-ref (car r) idx) (cdr r))) target-indices) (cdr r)))
                        (filter (lambda (r) (equal? gb-key-vals
                                                    (map (lambda (i) (list-ref (car r) i)) group-by-indices)))
                                table))]
                 [multiplicity (foldl (lambda (v r) (if (> v 0) 1 r)) 0 (map (lambda (r) (cdr r)) same-val-rows))]
                 [col-store-val-seg (transpose (map (lambda (r) (car r)) same-val-rows))])
            (cons col-store-val-seg multiplicity))
                  ; the multiplicity here indicates the multiplicity of the table 
                  ; after applying aggregation function instead of multiplicity of the rows
          (group-by-raw 
            (filter (lambda (r) 
                      (not (equal? gb-key-vals (map (lambda (i) (list-ref (car r) i)) group-by-indices)))) 
                    (cdr table))
            group-by-indices)))]))

;;; transpose a 2d list (from ij -> ji, e.g.)
(define (transpose list2d)
  (cond 
    [(equal? '() list2d) '()]
    [else (map (lambda (i) (map (lambda (r) (list-ref r i)) list2d))
               (range (length (car list2d))))]))


(define (dedup table)
  (cond
    [(equal? '() table) '()]
    [else 
      (let ([ele (car table)])
        (cond 
          [(equal? (cdr ele) 0)
           (dedup (cdr table))]
          [else 
            (cons (cons (car ele) 1)
                  (dedup (filter (lambda (x)(not (equal? (car ele) (car x))))
                                 (cdr table))))]))]))

(define (dedup-accum table)
  (cond 
    [(equal? '() table) '()]
    [else 
      (let ([ele (car table)])
        (cons 
          (cons (car ele)
                (foldl + 0 (map cdr (filter (lambda (x) (equal? (car ele) (car x))) table))))
          (dedup-accum 
            (filter (lambda (x) (not (equal? (car ele) (car x))))
                    (cdr table)))))]))

(define (projection indices table)
  (let ([proj-single (lambda (r)
                       (map (lambda (i)
                              (list-ref r i))
                            indices))])
    (map (lambda (p)
           (cons (proj-single (car p)) (cdr p)))
         table)))

; Given two tables, calculate the difference of table1 and table2 (with considering cardinanity)
(define (table-diff table1 table2)
  (let ([t1 (dedup-accum table1)])
    (map 
      (lambda (r) 
        (cons (car r) 
              (let ([cnt (- (cdr r) (get-row-count (car r) table2))])
                (cond [(> cnt 0) cnt]
                      [else 0])))) 
      t1)))

; Given a row and a table, count 
(define (get-row-count row-content table-content)
  (foldl + 0
         (map 
           (lambda (r) 
             (cond 
               [(equal? (car r) row-content) (cdr r)]
               [else 0]))
           table-content)))

(define (union-all table1 table2)
  (Table (get-table-name table1) 
         (get-schema table1) 
         (union-all-raw
           (Table-content table1)
           (Table-content table2))))

(define (union-all-raw content1 content2)
  (append content1 content2))

; equi join two tables, given a list of index pairs of form  [(c1, c1'), ..., (cn, cn')] 
; and the join condition is t1.c1 == t2.c1' and ... and t1.cn == t2.cn'
(define (equi-join content1 content2 index-pairs schema-size-1)
  (let ([join-result (xproduct-raw content1 content2)])
    (map (lambda (r)   
           (cons (car r)
                 (cond [(foldl && #t
                               (map
                                 (lambda (p)
                                   (equal? 
                                     (list-ref (car r) (car p)) 
                                     (list-ref (car r) (+ (cdr p) schema-size-1)))) 
                                 index-pairs)) 
                        (cdr r)]
                       [else 0])))
         join-result)))

; left outer join on two tables
(define (left-outer-join table1 table2 index1 index2)
  (let* ([content1 (Table-content table1)]
         [content2 (Table-content table2)])
    (Table 
      (string-append (get-table-name table1)
                     (get-table-name table2))
      (schema-join table1 table2) 
      (left-outer-join-raw content1 content2 index1 index2 (length (get-schema table1)) (length (get-schema table2))))))

; another version of left-outer-join
(define (left-outer-join-2 table1 table2 table12)
  (let* ([content1 (Table-content table1)]
         [content2 (Table-content table2)]
         [content12 (Table-content table12)])
    (Table
      (string-append (get-table-name table1)
                     (get-table-name table2))
      (schema-join table1 table2)
      (adding-null-rows content1 content2 content12 (length (get-schema table1)) (length (get-schema table2))))))


; left outer join two tables based on index1 and index2, this is raw because content1 content2 contains no table schema
(define (left-outer-join-raw content1 content2 index1 index2 schema-size-1 schema-size-2)
  (let ([content12 (equi-join content1 content2 (list (cons index1 index2)) schema-size-1)])
    (adding-null-rows content1 content2 content12 schema-size-1 schema-size-2)))

; content12 is the join result of content1 and content2 under come condition, 
;this functions helps extending the join result with rows in content1 but not in content 2
(define (adding-null-rows content1 content2 content12 schema-size-1 schema-size-2)
  (let ([null-cols (map (lambda (x) sqlnull) (build-list schema-size-2 values))])
    (let ([diff-keys (dedup (table-diff (dedup content1) (dedup (projection (build-list schema-size-1 values) content12))))])
      (let ([extra-rows (projection (build-list schema-size-1 values) 
                                    (equi-join content1 diff-keys (build-list schema-size-1 (lambda (x) (cons x x))) schema-size-1))])
        (union-all-raw 
          content12
          (map (lambda (r) (cons (append (car r) null-cols) (cdr r))) extra-rows))))))

; extend each row in the table with extended-element-list,
; e.g. each row will be (row ++ eel)
(define (extend-each-row table extra-elements)
  (map (lambda (r) (cons (append (car r) extra-elements) (cdr r))) table))

(define (cross-prod table1 table2)
  (let ([cross-single (lambda (p1)
                        (map (lambda (p2)
                               (let ([r1 (car p1)]
                                     [r2 (car p2)]
                                     [cnt (* (cdr p1) (cdr p2))])
                                 (cons (append r1 r2) cnt)))
                             table2))])
    (foldr append '() (map cross-single table1))))

;; calculate whether a list is distinct of not
(define (list-distinct? l)
  (cond 
    [(eq? l '()) #t]
    [else (&& (distinct-to-all-list (car l) (cdr l)) (list-distinct? (cdr l)))]))

(define (distinct-to-all-list x l)
  (foldl && #t (map (lambda (y) (not (eq? x y))) l)))
