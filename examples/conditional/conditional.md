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
    select d.DName as D, d.pn as P, p.Empl as E
    from Depts d, Payroll p
    where d.DName = p.PDept
);

create view V2 (
    select t.TMember as E, p.PDept as D, t.TProj as P
    from Teams t, Payroll p
    where t.TMember = p.Empl
)
```

Q1:
```
select t.TMember
from Depts d, Teams t
where pn = t.TProj and d.DName = "Security"
```

Q2
```
select v1.E
from V1 v1, V2 v2
where v1.D = "Security" and v1.P = v2.P and v1.E = v2.E and v1.D = v2.D
```

Q1 is only equivalent to Q1 if "Security" uses only its own employees on the projects it runs. 