Conditional SQL Rewrite
=======================

1. From Deutsch et al. (Penn TR 2001). NOTE: While supported by their chase algorithm, this rewrite cannot be expressed by our current language of preconditions.

    ```
    schema depts(DName:int, DProjs:int, pn:int);
    schema teams(TProj:int, TMember:int);
    schema payroll(PDept:int, Empl:int);
    table Depts(depts);
    table Teams(teams);
    table Payroll(payroll)；
    ```

    ```
    create view V1 (
        SELECT d.DName as D, d.pn as P, p.Empl as E
        FROM Depts d, Payroll p
        WHERE d.DName = p.PDept
    );

    create view V2 (
        SELECT t.TMember as E, p.PDept as D, t.TProj as P
        FROM Teams t, Payroll p
        WHERE t.TMember = p.Empl
    )
    ```

    Q1:
    ```
    SELECT t.TMember
    FROM Depts d, Teams t
    WHERE pn = t.TProj and d.DName = "Security"
    ```

    Q2
    ```
    SELECT v1.E
    FROM V1 v1, V2 v2
    WHERE v1.D = "Security" and v1.P = v2.P and v1.E = v2.E and v1.D = v2.D
    ```

    Q1 is only equivalent to Q1 if "Security" uses only its own employees on the projects it runs. 


2. Using foreign key to do join elimination. [blog article about oracle](https://danischnider.wordpress.com/2015/12/01/foreign-key-constraints-in-an-oracle-data-warehouse/)

    Assume a fact table SALES and 3 dimension tables PRODUCTS, CUSTOMERS and TIMES. There are 3 foreign keys (prod_id, cust_id, time_id) in SALES referring to primary keys of each demension table. 

    (I removed group by in the original queries for readablity).

    Q1
    ```
    SELECT p.prod_cat, s.amount_sold
    FROM sales s, product p, customers c, times t
    WHERE s.prod_id = p.prod_id AND s.cust_id = c.cust_id AND s.time_id = c.time_id AND
        t.calendar_year = 2014 
    ```

    Q2
    ```
    SELECT p.prod_cat, s.amount_sold
    FROM sales s, product p, times t
    WHERE s.prod_id = p.prod_id AND s.time_id = c.time_id AND t.calendar_year = 2014 
    ```

3. Rewrite using Index (An architecture for query optimization, Rosenthal etc SIGMOD 82)

    Assume payroll(ssno:int, deptno:int, ??), applicant(ssno:int, jobtitile:int, officeno:int, ??).

    Q1
    ``` 
        SELECT *
        FROM payroll, applicant
        WHERE payroll.ssno = applicant.ssno AND payroll.deptno = 29
    ```

    Q2
    ```
        CREATE VIEW idx_payroll(
        SELECT ssno, deptno
        FROM payroll
        );

        SELECT 
        FROM payroll, idx_payroll, applicant
        WHERE payroll.ssno = idx.ssno AND applicant.ssno = payroll.ssno AND 
            idx_payroll.deptno = 29 
    ```

4. Remove redundant join attribute. (Example 2.2, Query processing utilizing dependencies and horizontal decomposition, Kambayashi etc SIGMOD 83)

    The paper assumes a FD: A -> B. Here we assume that A is the key of R2 and R3.

    Q1
    ```
        SELECT R3.A, R3.B
        FROM R1, R2, R3
        WHERE R1.A = R2.A AND R2.A = R3.A AND R1.A = R3.A AND R2.B = R3.B
    ```

    Q2
    ```
        Select R3.A, R3.B
        FROM R1, R2, R3
        WHERE R1.A = R2.A AND R2.A = R3.A AND R1.A = R3.A
    ```


5. Remove redundant join attribute. (Example 3, Query processing utilizing dependencies and horizontal decomposition, Kambayashi etc SIGMOD 83)

    The paper assumes a FD: A -> J. Here we assume that A is the key of enrollment, class.

    schemas:
    ```
    supervisor(p:int, s:int, a:int);
    enrollment(s:int, j:int, a:int);
    class(j:int, p:int, a:int);
    office(p:int, r:int);
    ```

    Q1:
    ```
        SELECT s.p, s.s, s.a, e.j, c.p, o.r
        FROM s, e, c, o
        WHERE s.p = o.p AND s.s = e.s AND s.a = e.a AND e.j = c.j AND e.a = c.a AND
            s.p = c.p AND c.p = o.p 
    ```

    Q2:
    ```
        SELECT s.p, s.s, s.a, e.j, c.p, o.r
        FROM s, e, c, o
        WHERE s.p = o.p AND s.s = e.s AND s.a = e.a AND e.a = c.a AND
            s.p = c.p AND c.p = o.p 
    ```


6. Distinct pull up (Extensible/Rule Based Query Rewrite Optimization in Starburst, SIGMOD 92).
    
    Q1:
    ``` 
    CREATE VIEW itpv AS
    ( SELECT DISTINCT itp.itemn, pur.vendn
      FROM itp, pur
      WHERE itp.ponum = pur.ponum AND pur.odate > 85);
    
    SELECT itm.itmn, itpv.vendn 
    FROM itm, itpv
    WHERE itm.itemn = itpv.itemn AND itm.itemn > 1 and itm.itemn < 20;
    ```

    Q2
    ```
    SELECT DISTINCT itm.itmn, pur.vendn
    FROM itm, itp, pur
    WHERE itp.ponum = pur.ponum AND itm.itemn = itp.itemn AND pur.odate > 85 AND
        itm.itemn > 1 AND itm.itemn < 20;
    ```
    unfortunately, the condition is unknown. But there must be some preconditions since Q1 and Q2 are not universally equivalent.


7. Second distinct pull up (Extensible/Rule Based Query Rewrite Optimization in Starburst, SIGMOD 92).

    Q1
    ```
    CREATE VIEW itemprice AS
    ( SELECT DISTINCT itp.itemno, itp.NegotiatedPrice 
      FROM itp
      WHERE NegotiatedPrice > 1000);
    
    SELECT itemprice.NegotiatedPrice, itm.type
    FROM itemprice, itm
    WHERE itemprice.itemno = itm.itemno;
    ```

    Q2
    ```
    SELECT NeogitatePrice, type
    FROM
        (SELECT DISTINCT itp.NegotiatePrice, itm.type, itm.itemno
         FROM itp, itm
         WHERE itp.NegotiatedPrice > 1000 AND itp.itemno = itm.itemno)
    ```
 
8. Third distinct pull up (Extensible/Rule Based Query Rewrite Optimization in Starburst, SIGMOD 92).   

    Q1
    ```
    SELECT * FROM itp
    WHERE itm.itemn IN
        ( SELECT itl.itemn 
          FROM itl
          WHERE itl.wkcen = 468 AND itl.locan = 0);
    ```

    Q2
    ```
    SELECT DISTINCT itp.* 
    FROM itp, itl
    WHERE itp.itemn = itl.itemn AND itl.wkcen = 468 AND itl.locan = 0;
    ```

#### Other possible examples (requires more expressive language for preconditions)
1. 5 rules of semantic query optimizations (A System for semantic query optimizaiton, Shenoy etc, SIGMOD 87)