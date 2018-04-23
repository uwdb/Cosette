"""
test solver using examples
"""
import json
import solver
import unittest

def get_status(source):
    """ run program and get status
    """
    with open(source, 'r') as ofile:
        source = ofile.read()
        res = solver.solve(source)
        json_res = json.loads(res)
        return json_res["result"]


def run():
    #print(get_status("./examples/sqlrewrites/CQExample0.cos"))
    #print(get_status("./examples/sqlrewrites/SelfJoin0.cos"))
    #print(get_status("./examples/sqlrewrites/commutativeSelect.cos"))
    #print(get_status("./examples/sqlrewrites/inlineCorrelatedSubqueries.cos"))
    print(get_status("./examples/sqlrewrites/projectionDistributesOverUnion.cos"))
    #print(get_status("./examples/sqlrewrites/projectJoinTranspose.cos"))
    #print(get_status("./examples/sqlrewrites/joinCommute.cos"))
    #print(get_status("./examples/sqlrewrites/timesAndDiv.cos"))
    #print(get_status("./examples/sqlrewrites/countProject.cos"))
    #print(get_status("./examples/calcite/testAggregateConstantKeyRule2.cos"))
    #print(get_status("./examples/calcite/testRemoveSemiJoinRightWithFilter.cos"))
    #print(get_status("./examples/calcite/testAggregateGroupingSetsProjectMerge.cos"))
    #print(get_status("./examples/sqlrewrites/aggOnExpr.cos"))
    #print(get_status("./examples/calcite/testRemoveSemiJoinRight.cos"))
    #print(get_status("./examples/sqlrewrites/havingToWhere.cos"))
    #print(get_status("./examples/sqlrewrites/pullsubquery.cos"))
    #print(get_status("./examples/inequal_queries/344-exam-1.cos"))
    #print(get_status("./examples/inequal_queries/countbug.cos"))
    #print(get_status("./examples/inequal_queries/inline-exists.cos"))
    #print(get_status("./examples/inequal_queries/issue29.cos"))
    #print(get_status("./examples/sqlrewrites/unionEmpty.cos"))
    #print(get_status("./examples/inequal_queries/string_ex1.cos"))

if __name__ == '__main__':
    run()
