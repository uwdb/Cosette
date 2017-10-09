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



class EndToEndTests(unittest.TestCase):
    """ End to end tests for the solver
    """

    # equal queries
    def test_cq_ex0(self):
        """ CQExample0 """
        self.assertEqual(
            get_status("./examples/sqlrewrites/CQExample0.cos"), 'EQ', "CQExample0")

    def test_sj0(self):
        """ SelfJoin0 """
        self.assertEqual(
            get_status("./examples/sqlrewrites/SelfJoin0.cos"), 'EQ', "SelfJoin0")

    def test_comm_sel(self):
        """ commutativeSelect """
        self.assertEqual(
            get_status("./examples/sqlrewrites/commutativeSelect.cos"), 'EQ', "commutativeSelect")

    def test_inline_subq(self):
        """ inlineCorrelatedSubqueries """
        self.assertEqual(
            get_status("./examples/sqlrewrites/inlineCorrelatedSubqueries.cos"), 'EQ',
            "inlineCorrelatedSubqueries")

    def test_dist_proj_over_union(self):
        """ projectionDistributesOverUnion.cos~ """
        self.assertEqual(
            get_status("./examples/sqlrewrites/projectionDistributesOverUnion.cos"), 'EQ',
            "projectionDistributesOverUnion")

    def test_proj_join_trans(self):
        """ test project join transpose """
        self.assertEqual(
            get_status("./examples/sqlrewrites/projectJoinTranspose.cos"),
            'EQ', "project_join_transpose")

    def test_join_commmute(self):
        """ test project join commute """
        self.assertEqual(
            get_status("./examples/sqlrewrites/joinCommute.cos"), 'EQ', "join_commute")

    def test_times_div(self):
        """ test times and  div """
        self.assertEqual(
            get_status("./examples/sqlrewrites/timesAndDiv.cos"), 'EQ', "timesAndDiv")

    def test_count_proj(self):
        """ test count proj """
        self.assertEqual(
            get_status("./examples/sqlrewrites/countProject.cos"), 'EQ', "countProject")

    def test_agg_constant_key_rule_2(self):
        """ testAggregateConstantKeyRule2 from calcite """
        self.assertEqual(
            get_status("./examples/calcite/testAggregateConstantKeyRule2.cos"), 'EQ',
            "testAggregateConstantKeyRule2")

    def test_group_set_project_merge(self):
        """ testAggregateGroupingSetsProjectMerge from calcite """
        status = get_status("./examples/calcite/testAggregateGroupingSetsProjectMerge.cos")
        self.assertNotEqual(status, 'NEQ', "testAggregateGroupingSetsProjectMerge")
        self.assertNotEqual(status, 'ERROR', "testAggregateGroupingSetsProjectMerge")

    # inequal sql queries
    def test_344_exam_0(self):
        """ 344-exam-1 """
        self.assertEqual(
            get_status("./examples/inequal_queries/344-exam-1.cos"), 'NEQ', "344-exam-1")

    def test_countbug(self):
        """ countbug """
        self.assertEqual(
            get_status("./examples/inequal_queries/countbug.cos"), 'NEQ', "countbug")

    def test_syntax_error(self):
        """ test syntax error"""
        wrong_query = """
        schema s1(x:int, y:int);
        table a(s1);                   -- table a of schema s1 

        query q1                       -- query 1 
        `select                                     
         from a`;                                          
  
        query q2                       -- query 2 
        `select x as ax                                    
        from a`;                                              
  
        verify q1 q2;                  -- verify the equivalence """
        res = solver.solve(wrong_query)
        json_res = json.loads(res)
        self.assertEqual(json_res["result"], 'ERROR', "test syntax error")

    def test_exist(self):
        """ test exist """
        self.assertEqual(
            get_status("./examples/inequal_queries/inline-exists.cos"), 'NEQ', "inline-exists")

    def test_issue29(self):
        """ test issue 29 """
        self.assertEqual(
            get_status("./examples/inequal_queries/issue29.cos"), 'NEQ', "issue29-union")

    def test_union_empty(self):
        """ test union empty, for now at least it should not be NEQ, wait Coq part to return EQ """
        self.assertNotEqual(
            get_status("./examples/sqlrewrites/unionEmpty.cos"), 'NEQ', "union_empty")

if __name__ == '__main__':
    unittest.main()
