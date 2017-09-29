"""
Generate cos files from calcite test cases
"""

import json
from pprint import pprint

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

def gen_cos_files():
    """
    generate cos file
    """
    with open('calcite_tests.json') as input_file:
        data = json.load(input_file)

    pprint(data)

if __name__ == '__main__':
    gen_cos_files()
