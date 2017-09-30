Calcite Tests
=============

`calcite_test.json` contains test cases of [Apache Calcite](https://calcite.apache.org/), a query optimizer generator. The test cases are from https://github.com/apache/calcite/blob/master/core/src/test/java/org/apache/calcite/test/RelOptRulesTest.java . Each element of has 3 fields:

1. `name`: corresponding to the test name in `RelOptRuleTest.java`.
2. `q1`: converted from query plan (not the input SQL) before optimizer's rewrite.
3. `q3`: converted from query plan after optimzier's rewrite.

The following preprocessing has been done in `calcite_test.json`.

1. Remove the multi-level catalog, e.g. `CATALOG.SALES.EMP` becomes `EMP`.
2. Convert compound column to normal column. e.g. `F1.A0` becomes `F1_A0`.