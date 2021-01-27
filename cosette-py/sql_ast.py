import random
from pprint import pprint
import copy

def gen_fresh_name(base_name, used_names):
    if base_name not in used_names:
        new_name = base_name
    else:
        for i in range(2, 10000):
            if f"{base_name}_{i}" in used_names:
                continue
            new_name = f"{base_name}_{i}"
            break
    used_names.append(new_name)
    return new_name

def gen_name_mapping(old_name_sets, new_names):
    # old names is a list of set
    # new names is a list of strings
    mapping = {}
    for old_names, new_name in zip(old_name_sets, new_names):
      for old_name in old_names:
        mapping[old_name] = new_name
    return mapping
    
class TableOp():
    def tbl_op_dispatcher(s_exp):
        if s_exp[0] == "table_or_subquery":
            if s_exp[1][0] == 'table_name':
                tbl = TableReference(s_exp)
                if 'as' in s_exp:
                    tbl.alias = s_exp[3][1].replace("\'", "").replace("\"", "")
                elif len(s_exp) > 2 and type(s_exp[2]) == list and s_exp[2][0] == 'table_alias':
                    tbl.alias = s_exp[2][1].replace("\'", "").replace("\"", "")
            else: 
                tbl = SelectStatement(s_exp[1][0])
                if 'as' in s_exp:
                    tbl.alias = s_exp[3][1].replace("\'", "").replace("\"", "")
                elif len(s_exp) > 2 and type(s_exp[2]) == list and s_exp[2][0] == 'table_alias':
                    tbl.alias = s_exp[2][1].replace("\'", "").replace("\"", "")
            return tbl
        elif s_exp[0] == "join_clause":
            return JoinTable.from_s_exp(s_exp)
        
        
class RenamedTable(TableOp):
    def __init__(self, name, table, cols):
        self.name = name
        self.table = table
        self.cols = cols # these are invented alias names 

    def infer_out_schema(self, schema):
#         return self.table.infer_out_schema(schema)
        return [set([f"{self.name}.{c}", c]) for c in self.cols]

    def rename(self, schema, used_table_names):
        return self.table.rename(schema, used_table_names)
    
    def rename_ops(self, mapping):
        pass
    
    def to_rkt(self, schema):
        return "(AS " + self.table.to_rkt(schema) + "\n[\"" + self.name + "\" (list " + " ".join(["\"" + col + "\"" for col in self.cols]) + ")])"
            
class TableReference(TableOp):
    def __init__(self, s_exp):
        self.name = s_exp[1][1][1]
        if len(s_exp) > 2:
            self.alias = s_exp[2][1]
        else:
            self.alias = None
            
    def infer_out_schema(self, schema):
        tbl_schema = schema[self.name]
        to_return = []
        for col in tbl_schema:
            full_name = self.alias + "." + col if self.alias else self.name + "." + col
            to_return.append(set([full_name, col]))

        return to_return

    def rename(self, schema, used_table_names):
        tbl_schema = schema[self.name]
        tbl_name = self.alias if self.alias else self.name
        
        new_table_name = gen_fresh_name(tbl_name, used_table_names)
        
        # collecting old names
        old_names = [set([c, f"{tbl_name}.{c}"]) for c in tbl_schema]
        new_names = [f"{new_table_name}.{c}" for c in tbl_schema]
      
        mappings = gen_name_mapping(old_names, new_names)
        
        return RenamedTable(new_table_name, self, list(tbl_schema.keys())), mappings, used_table_names

    def rename_ops(self, mapping):
        pass
    
    def to_rkt(self, schema):
        return "(NAMED " + self.name + ")"

        
class JoinTable(TableOp):
    def __init__(self, left_tbl, right_tbl, join_op, constraint = None):
        self.left_tbl = left_tbl
        self.right_tbl = right_tbl
        self.join_op = join_op
        self.constraint = constraint
        
    @classmethod
    def from_s_exp(cls, s_exp):
        left_tbl = TableOp.tbl_op_dispatcher(s_exp[1])
        join_op = s_exp[2][1:]
        right_tbl = TableOp.tbl_op_dispatcher(s_exp[3])
        if "inner" in join_op:
            if type(s_exp[4]) == list:
                constraint = PredicateOp.pred_op_dispatcher(s_exp[4])
            else:
                constraint = None
            cross_table = cls(left_tbl, right_tbl, 'cross')
            to_return = SelectStatement([], wrap = True, wrap_tbl = cross_table, wrap_constraints = constraint)
            return to_return
        else:
            if type(s_exp[4]) == list:
                constraint = PredicateOp.pred_op_dispatcher(s_exp[4])
            else:
                constraint = None
            return cls(left_tbl, right_tbl, join_op, constraint)

    def infer_out_schema(self, schema):        
        left_cols = self.left_tbl.infer_out_schema(schema)
        right_cols = self.right_tbl.infer_out_schema(schema)
        left_cols_set = set()
        right_cols_set = set()
        for col_set in left_cols:
             left_cols_set = left_cols_set.union(col_set)
        for col_set in right_cols:
             right_cols_set = right_cols_set.union(col_set)
        duplicate_col_names = left_cols_set & right_cols_set
        
        if hasattr(self, "alias") and self.alias:
            name = self.alias
        else:
            name = None
        
        used_names = set()
        non_referrables = [set() for i in range(len(left_cols + right_cols))]
        for index, colset in enumerate(left_cols + right_cols):
            for col_name in colset:
                if col_name in used_names:
                    non_referrables[index].add(col_name)
                else:
                    used_names.add(col_name)
            
        to_return = left_cols + right_cols
        if not name:
            to_return = [{c for c in nameset if c not in non_refs} for nameset, non_refs in zip(to_return, non_referrables)]
        else:
            to_return = [set([f'{name}.{c}' for c in nameset if c not in non_refs and "." not in c] 
                             + [c for c in nameset if c not in non_refs and '.' in c]) for nameset, non_refs in zip(to_return, non_referrables)]
#         for index, nameset in enumerate(left_cols):
#             for col in nameset:
#                 if col in duplicate_col_names:
#                     if name:
#                         to_return[index].union(set([col, name + "." + col]))
#                     else:
#                         to_return[index].union(set([col]))
        return to_return
    
    
    def rename(self, schema, used_table_names):
        left_cols_old = self.left_tbl.infer_out_schema(schema)
        right_cols_old = self.right_tbl.infer_out_schema(schema)
        my_cols_old = self.infer_out_schema(schema)
        
        self.left_tbl, mappings_left, used_table_names = self.left_tbl.rename(schema, used_table_names)
        self.right_tbl, mappings_right, used_table_names = self.right_tbl.rename(schema, used_table_names)
        
        left_cols_new = self.left_tbl.infer_out_schema(schema)
        right_cols_new = self.right_tbl.infer_out_schema(schema)
        
        self.rename_ops({**mappings_left, **mappings_right})
        
        new_table_name = gen_fresh_name(self.alias if (hasattr(self, "alias") and self.alias) else "t", used_table_names)
        
        mappings = {}        
        # the list of new names
        column_list = []
        used_col_names = []
        for index, col_set in enumerate(my_cols_old):
            old_full_name = [col for col in col_set if "." in col]
            old_short_name = [col for col in col_set if "." not in col]
            base_name = old_full_name[0].split(".")[-1] if len(old_full_name) > 0 else "c"
            new_name = gen_fresh_name(base_name, used_col_names)
            
            for old_name in col_set:
                mappings[old_name] = new_table_name + "." + new_name
            column_list.append(new_name)

#         print("Join table mappings:")
#         pprint(mappings)
      
        return RenamedTable(new_table_name, self, column_list), mappings, used_table_names 

    def rename_ops(self, mapping):
        if self.constraint:
            self.constraint.rename_ops(mapping)
            
    def to_rkt(self, schema):
        if "left" in self.join_op:
            op = "LEFT-OUTER-JOIN"
        else:
            op = "JOIN"
             
        return f"({op} {self.left_tbl.to_rkt(schema)} {self.right_tbl.to_rkt(schema)} {self.constraint.to_rkt(schema) if self.constraint else ''})"
    

class SelectStatement(TableOp):
    def __init__(self, entire_s_exp, wrap = False, wrap_tbl = None, wrap_constraints = None):
        if wrap:
            self.columns = [AllColumn()]
            self.col_names = [None]
            self.tables = [wrap_tbl]
            self.tbl_names = [None]
            self.subquery_tree = wrap_tbl
            self.where_tree = wrap_constraints
            self.group_col = None
            self.having_tree = None
            self.order_cols = []
            self.ordering_dir = []
        else:
            self.from_s_exp(entire_s_exp)

    
    def from_s_exp(self, entire_s_exp):
        s_exp = entire_s_exp[1]

        select_index = s_exp.index('select')
        from_index = s_exp.index('from')
        self.columns = []
        self.col_names = []
                    
        for term in s_exp[select_index:from_index]:
            if type(term) == list and term[0] == 'result_column':
                self.columns.append(ColOp.col_op_dispatcher(term[1]))
                if "as" in term:
                    alias = term[term.index("as") + 1][1]
                    alias = alias.replace("\'", "").replace("\"", "")
                    self.col_names.append(alias)
                elif len(term) > 2 and type(term[2]) == list and term[2][0] == 'column_alias':
                    alias = term[2][1]
                    alias = alias.replace("\'", "").replace("\"", "")
                    self.col_names.append(alias)
                else:
                    self.col_names.append(None)

        self.tables = []
        self.tbl_names = [] 
        
        if "where" in s_exp:
            where_index = s_exp.index('where')
            for term in s_exp[from_index+1:where_index]:
                if type(term) == list:
                    self.tables.append(TableOp.tbl_op_dispatcher(term))
                    if hasattr(self.tables[-1], "alias"):
                        self.tbl_names.append(self.tables[-1].alias)
                    else:
                        self.tbl_names.append(None)
        else:
            for term in s_exp[from_index+1:]:
                if type(term) == list:
                    self.tables.append(TableOp.tbl_op_dispatcher(term))
                    if hasattr(self.tables[-1], "alias"):
                        self.tbl_names.append(self.tables[-1].alias)
                    else:
                        self.tbl_names.append(None)
        if len(self.tables) > 1:
            self.tables[0].alias = self.tbl_names[0]
            self.tables[1].alias = self.tbl_names[1]
            self.subquery_tree = JoinTable(self.tables[0], self.tables[1], 'cross')
            if len(self.tables) > 2:
                for i, tbl in enumerate(self.tables[2:]):
                    tbl.alias = self.tbl_names[i+2]
                    self.subquery_tree = JoinTable(left_tbl = self.subquery_tree, right_tbl = tbl, join_op = 'cross')
        else:
            self.subquery_tree = self.tables[0]
            self.subquery_tree.alias = self.tbl_names[0]

        if "where" in s_exp:
            self.where_tree = PredicateOp.pred_op_dispatcher(s_exp[where_index+1])
        else:
            self.where_tree = None

        if "group" in s_exp:
            groupby_index = list(filter(lambda i: s_exp[i] == 'group' and s_exp[i+1] == 'by', range(len(s_exp)-2)))[0]
            if "having" in s_exp:  
                having_index = s_exp.index('having')
                self.group_col = [ColOp.col_op_dispatcher(col) for col in s_exp[groupby_index + 2:having_index]]
            else:
                self.group_col = [ColOp.col_op_dispatcher(col) for col in s_exp[groupby_index + 2:]]
        else:
            self.group_col = None
        
        if "having" in s_exp:
            having_index = s_exp.index('having')
            self.having_tree = PredicateOp.pred_op_dispatcher(s_exp[having_index+1])
        else:
            self.having_tree = None

        self.order_cols = []
        self.ordering_dir = []
        if 'order' in entire_s_exp:
            orderby_index = list(filter(lambda i: entire_s_exp[i] == 'order' and entire_s_exp[i+1] == 'by', range(len(entire_s_exp)-2)))[0]
            if "limit" in entire_s_exp:
                end = entire_s_exp.index('limit')
            else:
                end = len(entire_s_exp)
            for term in entire_s_exp[orderby_index+2:end]:
                if type(term) == list and term[0] == "ordering_term":
                    self.order_cols.append(ColOp.col_op_dispatcher(term[1]))
                    if len(term) > 2:
                        self.ordering_dir.append(term[2])
                    else:
                        self.ordering_dir.append("asc")

        if 'limit' in entire_s_exp:
            limit_index = entire_s_exp.index('limit')
            self.limit = entire_s_exp[limit_index+1][1][1]

    
    def infer_out_schema(self, schema):
        to_return = []
        if type(self.columns[0]) == AllColumn:
            schema = self.subquery_tree.infer_out_schema(schema)
            to_return = [{col for col in nameset if "." not in col} for nameset in schema] # TODO: pass through names currently implemented
            to_return = [{col for col in nameset} for nameset in schema]
        else:
            for col, col_name in zip(self.columns, self.col_names):
                if col_name:
                    to_return.append(set([col_name]))
                else:
                    if type(col) in [UnaryColumnOp, BinaryColumnOp, ConstantColumn]:
                        to_return.append(set())
                    else:
                        to_return.append(set([col.name]))
                    
        if hasattr(self, "alias") and self.alias:
            for col in to_return:
                if col:
                    col.add(self.alias + "." + next(iter(col)))
        return to_return

    def rename(self, schema, used_table_names):
        child_old_names = self.subquery_tree.infer_out_schema(schema)
        my_old_names = self.infer_out_schema(schema)
        
        self.subquery_tree, child_mappings, used_table_names = self.subquery_tree.rename(schema, used_table_names)
        child_new_names = self.subquery_tree.infer_out_schema(schema)
        
        # print("My child mappings are", child_mappings)
        self.rename_ops(child_mappings, child_new_names)

        new_table_name = gen_fresh_name(self.alias if (hasattr(self, "alias") and self.alias) else "t", used_table_names)

        mappings = {}
        column_list = []
        used_col_names = []
        #print("My old names are", old_names)
        for index, col_set in enumerate(my_old_names):
            old_full_name = [col for col in col_set if "." in col]
            old_short_name = [col for col in col_set if "." not in col]
            if len(old_full_name) > 0:
                base_name = old_full_name[0].split(".")[-1]
            elif len(old_short_name) > 0:
                base_name = old_short_name[0]
            else:
                base_name = 'c'
            new_name = gen_fresh_name(base_name, used_col_names)

            for old_name in col_set:
                mappings[old_name] = new_table_name + "." + new_name

            column_list.append(new_name)
          
        # print(f"My mapping is [Select {new_table_name}]:")
        # pprint(mappings)
        
        # old names overwrites new names
        mappings_copy = copy.deepcopy(mappings)
        for name in child_mappings:
            mappings_copy[name] = child_mappings[name]
        
        self.rename_having(mappings_copy)
        
        return RenamedTable(new_table_name, self, column_list), mappings, used_table_names

    def rename_ops(self, mapping, new_names):
        replacement_col_names = []
        if type(self.columns[0]) == AllColumn:
            pass
        else:
            for col in self.columns:
                col.rename_ops(mapping)

        if self.where_tree:
            self.where_tree.rename_ops(mapping)

        if self.group_col:
            for col in self.group_col:
                col.rename_ops(mapping) 
                
    def rename_having(self, mapping):
        if self.having_tree:
            self.having_tree.rename_ops(mapping)

        for col in self.order_cols:
            col.rename_ops(mapping)
            
    def to_rkt(self, schema):
        where_part = "\nWHERE " + self.where_tree.to_rkt(schema) if self.where_tree else "\nWHERE (TRUE)" # TODO reference full names
        group_part = "\nGROUP-BY (list " + " ".join([col.to_rkt(schema) + " " for col in self.group_col])+ ")" if self.group_col else "" # TODO: reference full names
        if self.having_tree:
            having_part = "\nHAVING " + self.having_tree.to_rkt(schema) # TODO reference full names
        else:
            if self.group_col:
                having_part = "\nHAVING (TRUE)"
            else:
                having_part = ""
        if type(self.columns[0]) == AllColumn:
            select_part = "SELECT (VALS " + self.columns[0].to_rkt(schema, self.subquery_tree) + ")"
        else:
            select_part = "SELECT " + "(VALS " + " ".join([col.to_rkt(schema) for col in self.columns]) + ")"
        return "(" + select_part + "\nFROM " + self.subquery_tree.to_rkt(schema) + where_part + " " + group_part + " " + having_part + ")"
            

class ColOp():
    def col_op_dispatcher(s_exp):
        if s_exp == "*" or s_exp == "[*]":
            return AllColumn()
        assert s_exp[0] == "expr"
        if s_exp[1][0] == "column_name":
            return Column(s_exp[1])
        elif s_exp[1][0] == "literal_value":
            return ConstantColumn(s_exp[1])
        elif s_exp[1][0] == "function_name" and len(s_exp) == 3:
            return UnaryColumnOp(s_exp)
        elif '.' in s_exp:
            return Column(s_exp, table = True)
        elif len(s_exp) == 4:
            return BinaryColumnOp(s_exp)       

class Column(ColOp):
    def __init__(self, s_exp, table = False, direct = False, name = None):
        if direct:
            self.name = name
            self.table = None
        elif not table:
            assert s_exp[0] == "column_name"
            self.name = s_exp[1][1] if type(s_exp[1][1]) == str else s_exp[1][1][0][1]
            self.table = None
        else:
            assert s_exp[1][0] == "table_name"
            self.name = s_exp[3][1][1]
            self.table = s_exp[1][1][1]

    def rename_ops(self, mapping):
        if self.table:
            new_name = mapping[self.table + "." + self.name] 
        else:
            new_name = mapping[self.name] 
        self.table = new_name.split(".")[0]
        self.name = new_name.split(".")[1]
       
      
    def to_rkt(self, schema):
        return "\"" + (self.table + "." + self.name if self.table else self.name) + "\""
        
        
class ConstantColumn(ColOp):
    def __init__(self, s_exp):
        assert s_exp[0] == "literal_value"
        self.value = s_exp[1]
        
    def to_rkt(self, schema):
        return str(self.value)
    
    def rename_ops(self, mapping):
        pass
    
class UnaryColumnOp(ColOp):
    def __init__(self, s_exp):
        self.op = s_exp[1][1][1]
        self.col_ops = []
        for child in s_exp[2]:
            self.col_ops.append(ColOp.col_op_dispatcher(child))

    def rename_ops(self, mapping):
        # If child is an all column, replace it simply with just any 1 column which can be found in mapping's values. 
        for child in self.col_ops:
            if type(child) == AllColumn:
                key = next(iter(mapping))
                self.col_ops = [Column(None, False, direct = True, name = mapping[key])] # this is a hacky solution to replace count(*) with any column -- will not support NaNs!
                break
            else:
                child.rename_ops(mapping)
            
    def to_rkt(self, schema):
        return "(" + self.op.upper() + " " + " ".join(["\"" + (col.table + "." + col.name if col.table else col.name) + "\""  for col in self.col_ops]) + ")"
            
class BinaryColumnOp(ColOp):
    def __init__(self, s_exp):
        self.op = s_exp[2]
        if self.op == "==":
            self.op = "="
        self.left_col_op = ColOp.col_op_dispatcher(s_exp[1])
        self.right_col_op = ColOp.col_op_dispatcher(s_exp[3])

    def rename_ops(self, mapping):
        self.left_col_op.rename_ops(mapping)
        self.right_col_op.rename_ops(mapping)
        
    def to_rkt(self, schema):
        return "(BINOP " + self.left_col_op.to_rkt(schema) + " " + self.op + " " + self.right_col_op.to_rkt(schema) + ")"
    

class AllColumn(ColOp):
    def __init__(self):
        pass

    def rename_ops(self, mapping):
        pass
    
    def to_rkt(self, schema, table):
        table_schema = table.infer_out_schema(schema)
        full_names = [{colname for colname in colset if "." in colname}.pop() for colset in table_schema]
        to_return = ""
        for full_name in full_names:
            to_return += f"\"{full_name}\" "
        return to_return[:-1]
    
class PredicateOp():
    def pred_op_dispatcher(s_exp):
        if s_exp[0] == 'join_constraint':
            return JoinPredicate(s_exp)
        assert s_exp[0] == "expr"
        s_exp = find_ultimate_pred(s_exp)
        if 'and' in s_exp:
            return AndPred(s_exp)
        elif 'or' in s_exp:
            return OrPred(s_exp)
        elif s_exp[1][0] == 'unary_operator' and s_exp[1][1] == 'not':
            return NotPred(s_exp)
        elif "like" in s_exp:
            return LikePredicate(s_exp)
        else:
            return Predicate(s_exp)
        

class JoinPredicate(PredicateOp):
    def __init__(self, s_exp):
        assert s_exp[0] == 'join_constraint'
        pred_stmt = s_exp[2]
        self.op = pred_stmt[2]
        if self.op == '==':
            self.op = '='
        self.left_pred_op = ColOp.col_op_dispatcher(pred_stmt[1])
        self.right_pred_op = ColOp.col_op_dispatcher(pred_stmt[3])
    
    def rename_ops(self, mapping):
        self.left_pred_op.rename_ops(mapping)
        self.right_pred_op.rename_ops(mapping)
        
    def to_rkt(self, schema):
        return "(BINOP " + self.left_pred_op.to_rkt(schema) + " " + self.op + " " + self.right_pred_op.to_rkt(schema) + ")"

def find_ultimate_pred(s_exp):
    assert s_exp[0] == "expr"
    if type(s_exp[1][0]) == list:
        return find_ultimate_pred(s_exp[1][0])
    else:
        return s_exp
    
class Predicate(PredicateOp):
    def __init__(self, s_exp):
        assert s_exp[0] == 'expr'
        pred_stmt = s_exp
        self.left_pred_op = ColOp.col_op_dispatcher(pred_stmt[1])
        if pred_stmt[2] == 'not':
            self.op = pred_stmt[2:4]
            self.right_pred_op = ColOp.col_op_dispatcher(pred_stmt[4])
        else:
            self.op = pred_stmt[2]
            self.right_pred_op = ColOp.col_op_dispatcher(pred_stmt[3])

    def rename_ops(self, mapping):
        self.left_pred_op.rename_ops(mapping)
        self.right_pred_op.rename_ops(mapping)

    def to_rkt(self, schema):
        return "(BINOP " + self.left_pred_op.to_rkt(schema) + " " + self.op + " " + self.right_pred_op.to_rkt(schema) + ")"
    
class LikePredicate(Predicate):
    def __init__(self, s_exp):
        assert s_exp[0] == 'expr'
        self.left_pred_op = ColOp.col_op_dispatcher(s_exp[1])
        if s_exp[2] == 'not':
            self.like = False
            self.pattern = s_exp[4][1][1]
        else:
            self.like = True
            self.pattern = s_exp[3][1][1]
    
    def rename_ops(self, mapping):
        self.left_pred_op.rename_ops(mapping)
        
    def to_rkt(self, schema):
        if self.like: 
            return "(TRUE)"
            return "(LIKEOP " + self.left_pred_op.to_rkt(schema) + " \"" + self.pattern + "\")" # TODO
        else:
            return "(TRUE)"
            return "(NOT (LIKEOP " + self.left_pred_op.to_rkt(schema) + " \"" + self.pattern + "\"))"
            
class AndPred(PredicateOp):
    def __init__(self, s_exp):
        self.left_pred_op = PredicateOp.pred_op_dispatcher(s_exp[1])
        self.right_pred_op = PredicateOp.pred_op_dispatcher(s_exp[3])

    def rename_ops(self, mapping):
        self.left_pred_op.rename_ops(mapping)
        self.right_pred_op.rename_ops(mapping)
        
    def to_rkt(self, schema):
        return "(AND " + self.left_pred_op.to_rkt(schema) + " " + self.right_pred_op.to_rkt(schema) + ")"
        
class OrPred(PredicateOp):
    def __init__(self, s_exp):
        self.left_pred_op = PredicateOp.pred_op_dispatcher(s_exp[1])
        self.right_pred_op = PredicateOp.pred_op_dispatcher(s_exp[3])
    
    def rename_ops(self, mapping):
        self.left_pred_op.rename_ops(mapping)
        self.right_pred_op.rename_ops(mapping)
        
    def to_rkt(self, schema):
        return "(OR " + self.left_pred_op.to_rkt(schema) + " " + self.right_pred_op.to_rkt(schema) + ")"
        
def NotPred(PredicateOp):
    def __init__(self, s_exp):
        pred_stmt = s_exp[2][1][0]
        self.op = pred_stmt[2]
        self.pred_op = PredOp.pred_op_dispatcher(pred_stmt[1])
    
    def rename_ops(self, mapping):
        self.pred_op.rename_ops(mapping)
        
    def to_rkt(self, schema):
        return "(NOT " + self.pred_op.to_rkt(schema) + ")"
 