Cosette DSL
==========================

Cosette DSL is designed to express SQL rewrite. Cosette runtime will compile Cosette DSL to HoTTSQL, 
an intermediate language and then calls SMT solver as well as the Coq proof assistant to try to falsify 
and prove the equivalence of two SQL queries.


### Syntax
TBD


### Examples
1. communitivity of select.

   ```
   schema s(??);
   table a(s);
   predicate b0(s);
   predicate b1(s);
   
   query q1 
   `SELECT * FROM (SELECT * FROM a x WHERE b0(x)) y WHERE b1(y)`;
   
   query q2
   `SELECT * FROM (SELECT * FROM a x WHERE b1(x)) y WHERE b0(y)`;
   
   verify q1 q2;
   ```

2. push filtering through aggregate.

   ```
   schema s(l:int, v:int, ??);
   table a(s);
   constant c:int;
   
   query q1 
   `SELECT * FROM (SELECT x.l as l, COUNT(x.v) as cnt FROM a x GROUP BY x.l) y
    WHERE y.l = c`;
   
   query q2
   `SELECT x.l as l, COUNT(v) as cnt FROM a x WHERE x.l = c GROUP BY x.l`;
   
   verify q1 q2;
   ```

3. magic self join.
   
   ```
   schema s(??);
   table a(s);
   
   
   query q1 
   `SELECT DISTINCT y.* FROM a x, a y`;
   
   query q2
   `SELECT DISTINCT * FROM a x`;
   
   verify q1 q2;
   ```

4. q1 cse 344 (expected a counter example).
   
   ```
   schema sp(uid:int, size:int);
   schema su(uid:int, uname:int, city:int);
   table picture(sp);
   table usr(su);

	query q1
   `SELECT x.uid, x.uname, (SELECT COUNT(*) FROM picture y WHERE x.uid = y.uid and y.size > 1000000)
    FROM usr x WHERE x.city = "Denver"`;
   
   query q2
   `SELECT x.uid, x.uname, COUNT(*)
    FROM usr x, picture y
	WHERE x.uid = y.uid and y.size > 1000000 and x.city = "Denver"
	GROUP BY x.uid, x.uname`;
  
   verify q1 q2;
   ```

5. pull subquery in from, this is interesting because we need to use CASTPRED in HoTTSQL
to express this rewrite rule.
   
   ```
   schema sr(??), ss(??);
   table r(sr);
   table s(ss);
   predicate b1(sr,ss);
   predicate b0(s);
   
   query q1
   `SELECT * FROM r y, (SELECT * FROM s x WHERE b0(x)) z WHERE b1(y, z)`;
   
   query q2
   `SELECT * FROM r x, s y WHERE b0(y) and b1(x, y)`;
   
   verify q1 q2;
   ```
