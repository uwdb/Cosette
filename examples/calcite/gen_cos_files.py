"""
Generate cos files from calcite test cases
"""

import json

SUPPORTED_TESTS = ["testUnionToDistinctRule",
                   "testAddRedundantSemiJoinRule",
                   "testPushFilterPastAgg",
                   "testPushFilterPastAggTwo",
                   "testPushFilterPastAggFour",
                   "testSemiJoinRuleExists",
                   "testPushProjectPastSetOp",
                   "testPushJoinThroughUnionOnLeft",
                   "testPushJoinThroughUnionOnRight",
                   "testMergeFilter",
                   "testMergeUnionAll",
                   "testPushSemiJoinPastJoinRuleLeft",
                   "testPushSemiJoinPastJoinRuleRight",
                   "testConvertMultiJoinRule",
                   "testReduceConstantsDup",
                   "testRemoveSemiJoin",
                   "testRemoveSemiJoinRight",
                   "testReduceConstantsNegated",
                   "testReduceConstantsNegatedInverted",
                   "testEmptyAggregate",
                   "testEmptyAggregateEmptyKey",
                   "testEmptyAggregateEmptyKeyWithAggregateValuesRule",
                   "testPushSumConstantThroughUnion",
                   "testPushSumNullableThroughUnion",
                   "testPushSumNullableNOGBYThroughUnion",
                   "testPushCountStarThroughUnion",
                   "testPushCountNullableThroughUnion",
                   "testPushMaxNullableThroughUnion",
                   "testPushMinThroughUnion",
                   "testPushSumCountStarThroughUnion",
                   "testPushSumConstantGroupingSetsThroughUnion",
                   "testPushSumNullableGroupingSetsThroughUnion",
                   "testPushCountStarGroupingSetsThroughUnion",
                   "testPushCountNullableGroupingSetsThroughUnion",
                   "testPushMaxNullableGroupingSetsThroughUnion",
                   "testPushMinGroupingSetsThroughUnion",
                   "testPushSumCountStarGroupingSetsThroughUnion",
                   "testPushCountFilterThroughUnion",
                   "testPullFilterThroughAggregate",
                   "testPullConstantThroughUnion",
                   "testPullConstantThroughUnion2",
                   "testPullConstantThroughUnion3",
                   "testAggregateProjectMerge",
                   "testAggregateGroupingSetsProjectMerge",
                   "testPullAggregateThroughUnion",
                   "testPullConstantIntoProject",
                   "testAggregateProjectPullUpConstants",
                   "testPushJoinCondDownToProject",
                   "testAggregateConstantKeyRule",
                   "testAggregateConstantKeyRule2",
                   "testExpandProjectScalar",
                   "testExpandFilterExists",
                   "testExpandFilterExistsSimple",
                   "testExpandFilterExistsSimpleAnd",
                   "testDecorrelateExists",
                   "testDecorrelateTwoExists",
                   "testDecorrelateTwoScalar",
                   "testExpandWhereComparisonCorrelated",
                   "testCustomColumnResolvingInCorrelatedSubQuery"]

# from MockCatalogReader.java
SCHEMA_TABLE_DECS = """
schema emp(empno:int, ename:int, job:int, mgr:int, hiredate:int, comm:int, sal:int, deptno:int, slacker:int);
schema dept(deptno:int, name:int);
schema bonus(ename:int, job:int, sal:int, comm:int);
schema account(acctno:int, type:int, balance:int);
schema t(k0:int, c1:int, f1_a0:int, f2_a0:int, f0_c0:int, f1_c0:int, f0_c1:int, f1_c2:int, f2_c3:int);
table emp(emp);
table dept(dept);
table bonus(bonus);
table account(account);
table t(t);
"""

def gen_cos_files():
    """
    generate cos file
    """
    with open('calcite_tests.json') as input_file:
        data = json.load(input_file)

    supported_tests = set(SUPPORTED_TESTS)

    count = 0
    for i in data:
        if i["name"] in supported_tests:
            print "writing {}.cos".format(i["name"])
            with open("{}.cos".format(i["name"]), 'w') as output_file:
                output_file.write("{}\n{}\n{}\n{}".format(
                    SCHEMA_TABLE_DECS,
                    gen_q_stmt("q1", i["q1"]),
                    gen_q_stmt("q2", i["q2"]),
                    gen_v_stmt("q1", "q2")))
                count += 1

    print "converted {} test cases to cosette programs.".format(count)


def gen_q_stmt(name, query):
    """
    return a string of query statement.
    """
    return "query {} `{}`;\n".format(name, query)


def gen_v_stmt(q1n, q2n):
    """
    return a string of verify statement.
    """
    return "verify {} {};\n".format(q1n, q2n)

if __name__ == '__main__':
    gen_cos_files()
