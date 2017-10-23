Conditional SQL Rewrite
=======================

1. From Deutsch et al. (Penn TR 2001) see `fkPennTR.cos`. 
    ```
    schema depts(DName:int, DProj:int);
    schema teams(TProj:int, TMember:int); -- TMember is a fk to payroll.Empl
    schema payroll(PDept:int, Empl:int); -- Empl is pk
    table Depts(depts);
    table Teams(teams);
    table Payroll(payroll)；
    ```

    ```
    create view V1 (
        SELECT d.DName as D, d.DProj as P, p.Empl as E
        FROM depts d, payroll p
        WHERE d.DName = p.PDept
    );

    create view V2 (
        SELECT t.TMember as E, p.PDept as D, t.TProj as P
        FROM teams t, payroll p
        WHERE t.TMember = p.Empl
    )
    ```

    Q1:
    ```
    SELECT t.TMember
    FROM Depts d, Teams t
    WHERE d.Dproj = t.TProj and d.DName = 'Security'
    ```

    Q2
    ```
    SELECT v1.E
    FROM V1 v1, V2 v2
    WHERE v1.D = 'Security' and v1.P = v2.P and v1.E = v2.E and v1.D = v2.D
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
        SELECT applicant.*
        FROM payroll, applicant
        WHERE payroll.ssno = applicant.ssno AND payroll.deptno = 29
    ```

    Q2
    ```
        CREATE VIEW idx_payroll(
        SELECT ssno, deptno
        FROM payroll
        );

        SELECT applicant.*
        FROM payroll, idx_payroll, applicant
        WHERE payroll.ssno = idx.ssno AND applicant.ssno = payroll.ssno AND 
            idx_payroll.deptno = 29 
    ```

4. Remove redundant join attribute. (Example 2.2, Query processing utilizing dependencies and horizontal decomposition, Kambayashi etc SIGMOD 83)

    The paper assumes a FD: A -> B. Here we assume that A is the key.

    Q1
    ```
        SELECT z.A, z.B
        FROM R1 x, R2 y, R2 z
        WHERE x.A = y.A AND y.A = z.A AND x.A = z.A AND y.B = z.B
    ```

    Q2
    ```
        Select z.A, z.B
        FROM R1 x, R2 x, R2 x
        WHERE x.A = y.A AND y.A = R3.A AND R1.A = R3.A
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