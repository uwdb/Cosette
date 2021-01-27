import sys
from antlr4 import *
from grammar.SQLiteLexer import SQLiteLexer
from grammar.SQLiteParser import SQLiteParser
from grammar.SQLiteListener import SQLiteListener
import re
from readlisp import readlisp, LispSymbol
import copy
import sys
import os
from sql_ast import *
from cosette import run_equiv_check
        
schema = {"indiv_sample_nyc": {
        "cmte_id": "int", 
        "transaction_amt": "int",
        "name": "str"
}, "comm": {
        "cmte_id": "int", 
        "cmte_nm": "int",
        "cand_id": "int"
},
    "cand": {"cand_name": "str", "cand_id": "int"}
}

preamble = """#lang rosette 
 
(require "../cosette.rkt" "../sql.rkt" "../evaluator.rkt" "../syntax.rkt") 
 
(provide ros-instance)
 
(current-bitwidth #f)
"""

answers = {"q1_a": {"rkt": """(SELECT (VALS "indiv_sample_nyc.cmte_id" "indiv_sample_nyc.transaction_amt" "indiv_sample_nyc.name") 
                         FROM (NAMED indiv_sample_nyc)
                         WHERE (AND (TRUE) 
                                    (TRUE)))""",
                    "like": {"name": {"like": ["%TRUMP%", "%DONALD%"]}}
                   },
          "q1_b": {"rkt": """(SELECT (VALS "indiv_sample_nyc.cmte_id" "indiv_sample_nyc.transaction_amt" "indiv_sample_nyc.name") 
                         FROM (NAMED indiv_sample_nyc)
                         WHERE (AND (TRUE)
                                    (AND (TRUE) (TRUE))))""",
                   "like": {"name": {"like": ["%TRUMP%", "%DONALD%"],
                                    "notlike": ['%INC%']}}
                  },
          "q1_c": {"rkt": """(AS 
                        (SELECT (VALS "indiv_sample_nyc.cmte_id" (SUM "indiv_sample_nyc.transaction_amt") (COUNT "indiv_sample_nyc.cmte_id"))
                         FROM (NAMED indiv_sample_nyc)
                         WHERE (AND (TRUE)
                                    (AND (TRUE) (TRUE)))
                         GROUP-BY (list "indiv_sample_nyc.cmte_id")
                         HAVING (TRUE)) ["q1c" (list "cmte_id" "total_amount" "num_donations")])""",
                  "order": "total_amount",
                  "direction": "desc",
                  "like": {"name": {"like": ["%TRUMP%", "%DONALD%"],
                                    "notlike": ['%INC%']}}
                  },
          "q1_d": {
                   "rkt": """(SELECT (VALS "t2.cmte_id" (SUM "t2.transaction_amt") (COUNT "t2.cmte_id") "t2.cmte_nm")
                         FROM (AS (SELECT (VALS "t.cmte_id" "t.cmte_nm" "t.cand_id" "t.cmte_id_2" "t.transaction_amt" "t.name")
                                   FROM (AS (JOIN (NAMED indiv_sample_nyc) (NAMED comm))
                                        ["t" (list "cmte_id" "transaction_amt" "name" "cmte_id_2" "cmte_nm" "cand_id")])
                                   WHERE (BINOP "t.cmte_id" = "t.cmte_id_2"))
                                ["t2" (list "cmte_id" "cmte_nm" "cand_id" "cmte_id_2" "transaction_amt" "name")])
                         WHERE (AND (TRUE) (AND (TRUE) (TRUE)))
                         GROUP-BY (list "t2.cmte_id") 
                         HAVING (TRUE))""",
                  "order": "total_amount",
                  "direction": "desc",
                   "like": {"name": {"like": ["%TRUMP%", "%DONALD%"],
                                    "notlike": ['%INC%']}}
                  },
          "q2_a": {"rkt": """(SELECT (VALS "t.cmte_id" (SUM "t.transaction_amt") (COUNT "t.cmte_id"))
                     FROM (AS (NAMED indiv_sample_nyc) ["t" (list "cmte_id" "transaction_amt" "name")])
                     WHERE (TRUE)
                     GROUP-BY (list "t.cmte_id") 
                     HAVING (TRUE))""",
                  "order": "count",
                  "direction": "desc",
                  "limit": 5,
                  "like": {"cmte_id": {"like": ["%5"]}}
                  },
          "q2_b": {"rkt": """(SELECT (VALS "t.cand_name" "t.cmte_nm") 
                     FROM (AS (JOIN (NAMED cand) (NAMED comm)) ["t" (list "cand_name" "cand_id" "cmte_id" "cmte_nm" "cand_id_2")])
                     WHERE (BINOP "t.cand_id" = "t.cand_id_2"))""",
                  "order": "cand_name",
                   "direction": "desc",
                   "limit": 5},
          "q2_c": {"rkt": """(SELECT (VALS "t.cand_name" "t.cmte_nm")
                     FROM (AS (LEFT-OUTER-JOIN (NAMED cand) (NAMED comm) (BINOP "cand.cand_id" = "comm.cand_id")) ["t" (list "cand_name" "cand_id" "cmte_id" "cmte_nm" "cand_id_2")])
                     WHERE (TRUE))""",
                  "order": "cand_name",
                   "direction": "desc",
                   "limit": 5},
          }


def pre_process_tree(query):
    query += "\n"
    query = re.sub("""(?!\()([^\s]+?\s+?(?:not\s)?like\s+?["'][^\s]+?["'])\s+?(?!\))""", r' (\1) ', query, flags = re.IGNORECASE)
    query = re.sub("""(?!\()([^\s]+?\s+?(?:not\s)?like\s*?["'][^\s]+?["'])\s*?(?!\))""", r' (\1) ', query, flags = re.IGNORECASE)
    query = re.sub("""(?!\()([^\s]+?\s+?(?:not\s)?like\s*?["']%[\w\d\s]+?%["'])\s*?(?!\))""", r' (\1) ', query, flags = re.IGNORECASE)
    query = query.replace(";", "")
    return query

        
def remove_lisp_symbol(l):
    if type(l) in [LispSymbol, int, float]:
        if type(l) == LispSymbol:
            return l.name.lower()
        else:
            return str(l)
    elif type(l) == list:
        return [remove_lisp_symbol(ls) for ls in l]
    else:
        print("Uhoh", type(l), l)
        
def get_parsed_tree(query, filename):
    cleaned_query = pre_process_tree(query)
    with open(filename, "w+") as f:
        f.write(cleaned_query)
    input_stream = FileStream(filename)
    lexer = SQLiteLexer(input_stream)
    stream = CommonTokenStream(lexer)
    parser = SQLiteParser(stream)
    tree = parser.parse()
    print("the query was", query)
    print("the cleaned query was", cleaned_query)    
    tree = remove_lisp_symbol(readlisp(tree.toStringTree(recog=parser)))
    return tree, query 

def generate_rkt_file(schema, preamble, query_1, query_2):
    schema_lines = ""
    tables = []
    for table in schema:
        col_str = " ".join(["\"" + col + "\"" for col in schema[table]])
        tables.append(table)
        schema_lines += f"(define {table}-info (table-info \"{table}\" (list " + col_str + ")))\n"

    info_list = " ".join([f"{table_info}-info" for table_info in tables])
    schema_lines += f"(define all-tables (list " + info_list + "))\n"

    query_1_updated = query_1
    for table in schema:
        query_1_updated = query_1_updated.replace(f"(NAMED {table})", f"(NAMED (list-ref tables {tables.index(table)}))")


    query_2_updated = query_2
    for table in schema:
        query_2_updated = query_2_updated.replace(f"(NAMED {table})", f"(NAMED (list-ref tables {tables.index(table)}))")


    query_1_updated = "(define (q1 tables)\n" + query_1_updated +")\n"
    query_2_updated = "(define (q2 tables)\n" + query_2_updated +")\n"

    final_line = "(define ros-instance (list q1 q2 all-tables))"
    
    result = preamble + schema_lines + query_1_updated + query_2_updated + final_line
    return result

def output_to_rkt(query, schema, question, output_file, sql_filename = "query.sql"):
    try:
        tree, cleaned_query = get_parsed_tree(query, sql_filename)
        select_s_exp = tree[1][1][1]
        query_tree = SelectStatement(select_s_exp)
        query_tree = query_tree.rename(schema, [])[0]
        result = query_tree.to_rkt(schema)
        rkt_file = generate_rkt_file(schema, preamble, answers[question]["rkt"], result)
        with open(output_file, "w+") as f:
            f.write(rkt_file)

        results = run_equiv_check(rkt_file, "/Users/alanliang/repos/Cosette/", 10)
        if results['status'] == "EQ":
            cosette_valid = True
        elif results['status'] == "NEQ":
            cosette_valid = False
        else:
            print(results['status'])
            cosette_valid = None

        limit_valid, order_col_valid, order_dir_valid, like_valid = None, None, None, None
        if "limit" in answers[question]:
            if hasattr(query_tree.table, 'limit') and query_tree.table.limit:
                if int(answers[question]["limit"]) != int(query_tree.table.limit):
                    limit_valid = False
                else:
                    limit_valid = True
            else:
                limit_valid = False
        
        if 'order' in answers[question]:
            if hasattr(query_tree.table, 'order_cols') and query_tree.table.order_cols:
                query_order_col = query_tree.table.order_cols[0]
                query_order_dir = query_tree.table.ordering_dir[0]
                if not answers[question]['order'] in query_order_col.name:
                    order_col_valid = False
                else:
                    order_col_valid = True
                if answers[question]['direction'] not in query_order_dir.lower():
                    order_dir_valid = False
                else:
                    order_dir_valid = True
            else:
                order_col_valid = False
                order_dir_valid = False

        if 'like' in answers[question]:
            like_valid = True
            like_dict = copy.deepcopy(answers[question]['like'])
            remaining_dict = traverse_like(query_tree.table.where_tree, like_dict, False)
            for col_ref in remaining_dict:
                if 'like' in remaining_dict[col_ref] and len(remaining_dict[col_ref]['like']) != 0:
                    like_valid = False
                if 'notlike' in remaining_dict[col_ref] and len(remaining_dict[col_ref]['notlike']) != 0:
                    like_valid = False

        return cosette_valid, limit_valid, order_col_valid, order_dir_valid, like_valid
    except:
        print("ERRORED OUT")
        print("My query is:\n", q)
        print(traceback.print_exc() )
        return None, None, None, None, None
    
def traverse_like(where_tree, like_dict, flipped):
    if type(where_tree) in [AndPred, OrPred]:
        like_dict = traverse_like(where_tree.left_pred_op, like_dict, flipped)
        like_dict = traverse_like(where_tree.right_pred_op, like_dict, flipped)
    elif type(where_tree) == NotPred:
        like_dict = traverse_like(where_tree.pred_op, like_dict, not flipped)
    elif type(where_tree) == Predicate:
        pass
    elif type(where_tree) == LikePredicate:
        col = where_tree.left_pred_op.name
        for col_ref in like_dict:
            if col_ref in col:
                likes = like_dict[col_ref]['like'] if 'like' in like_dict[col_ref] else []
                not_likes = like_dict[col_ref]['notlike'] if 'notlike' in like_dict[col_ref] else []
                if where_tree.like and not flipped:
                    pattern = where_tree.pattern.upper().replace("\"", "").replace("\'", "")
                    if pattern in likes:
                        likes.remove(pattern)
                elif not where_tree.like and flipped:
                    pattern = where_tree.pattern.upper().replace("\"", "").replace("\'", "")
                    if pattern in not_likes:
                        not_likes.remove(pattern)
                elif not where_tree.like and not flipped:
                    pattern = where_tree.pattern.upper().replace("\"", "").replace("\'", "")
                    if pattern in not_likes:
                        not_likes.remove(pattern)
                elif where_tree.like and flipped:
                    pattern = where_tree.pattern.upper().replace("\"", "").replace("\'", "")
                    if pattern in likes:
                        likes.remove(pattern)
                like_dict[col_ref]['like'] = likes
                like_dict[col_ref]['notlike'] = not_likes
    return like_dict
