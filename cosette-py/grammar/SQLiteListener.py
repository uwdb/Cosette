# Generated from grammar/SQLite.g4 by ANTLR 4.8
from antlr4 import *
if __name__ is not None and "." in __name__:
    from .SQLiteParser import SQLiteParser
else:
    from SQLiteParser import SQLiteParser

# This class defines a complete listener for a parse tree produced by SQLiteParser.
class SQLiteListener(ParseTreeListener):

    # Enter a parse tree produced by SQLiteParser#parse.
    def enterParse(self, ctx:SQLiteParser.ParseContext):
        pass

    # Exit a parse tree produced by SQLiteParser#parse.
    def exitParse(self, ctx:SQLiteParser.ParseContext):
        pass


    # Enter a parse tree produced by SQLiteParser#error.
    def enterError(self, ctx:SQLiteParser.ErrorContext):
        pass

    # Exit a parse tree produced by SQLiteParser#error.
    def exitError(self, ctx:SQLiteParser.ErrorContext):
        pass


    # Enter a parse tree produced by SQLiteParser#sql_stmt_list.
    def enterSql_stmt_list(self, ctx:SQLiteParser.Sql_stmt_listContext):
        pass

    # Exit a parse tree produced by SQLiteParser#sql_stmt_list.
    def exitSql_stmt_list(self, ctx:SQLiteParser.Sql_stmt_listContext):
        pass


    # Enter a parse tree produced by SQLiteParser#sql_stmt.
    def enterSql_stmt(self, ctx:SQLiteParser.Sql_stmtContext):
        pass

    # Exit a parse tree produced by SQLiteParser#sql_stmt.
    def exitSql_stmt(self, ctx:SQLiteParser.Sql_stmtContext):
        pass


    # Enter a parse tree produced by SQLiteParser#alter_table_stmt.
    def enterAlter_table_stmt(self, ctx:SQLiteParser.Alter_table_stmtContext):
        pass

    # Exit a parse tree produced by SQLiteParser#alter_table_stmt.
    def exitAlter_table_stmt(self, ctx:SQLiteParser.Alter_table_stmtContext):
        pass


    # Enter a parse tree produced by SQLiteParser#analyze_stmt.
    def enterAnalyze_stmt(self, ctx:SQLiteParser.Analyze_stmtContext):
        pass

    # Exit a parse tree produced by SQLiteParser#analyze_stmt.
    def exitAnalyze_stmt(self, ctx:SQLiteParser.Analyze_stmtContext):
        pass


    # Enter a parse tree produced by SQLiteParser#attach_stmt.
    def enterAttach_stmt(self, ctx:SQLiteParser.Attach_stmtContext):
        pass

    # Exit a parse tree produced by SQLiteParser#attach_stmt.
    def exitAttach_stmt(self, ctx:SQLiteParser.Attach_stmtContext):
        pass


    # Enter a parse tree produced by SQLiteParser#begin_stmt.
    def enterBegin_stmt(self, ctx:SQLiteParser.Begin_stmtContext):
        pass

    # Exit a parse tree produced by SQLiteParser#begin_stmt.
    def exitBegin_stmt(self, ctx:SQLiteParser.Begin_stmtContext):
        pass


    # Enter a parse tree produced by SQLiteParser#commit_stmt.
    def enterCommit_stmt(self, ctx:SQLiteParser.Commit_stmtContext):
        pass

    # Exit a parse tree produced by SQLiteParser#commit_stmt.
    def exitCommit_stmt(self, ctx:SQLiteParser.Commit_stmtContext):
        pass


    # Enter a parse tree produced by SQLiteParser#compound_select_stmt.
    def enterCompound_select_stmt(self, ctx:SQLiteParser.Compound_select_stmtContext):
        pass

    # Exit a parse tree produced by SQLiteParser#compound_select_stmt.
    def exitCompound_select_stmt(self, ctx:SQLiteParser.Compound_select_stmtContext):
        pass


    # Enter a parse tree produced by SQLiteParser#create_index_stmt.
    def enterCreate_index_stmt(self, ctx:SQLiteParser.Create_index_stmtContext):
        pass

    # Exit a parse tree produced by SQLiteParser#create_index_stmt.
    def exitCreate_index_stmt(self, ctx:SQLiteParser.Create_index_stmtContext):
        pass


    # Enter a parse tree produced by SQLiteParser#create_table_stmt.
    def enterCreate_table_stmt(self, ctx:SQLiteParser.Create_table_stmtContext):
        pass

    # Exit a parse tree produced by SQLiteParser#create_table_stmt.
    def exitCreate_table_stmt(self, ctx:SQLiteParser.Create_table_stmtContext):
        pass


    # Enter a parse tree produced by SQLiteParser#create_trigger_stmt.
    def enterCreate_trigger_stmt(self, ctx:SQLiteParser.Create_trigger_stmtContext):
        pass

    # Exit a parse tree produced by SQLiteParser#create_trigger_stmt.
    def exitCreate_trigger_stmt(self, ctx:SQLiteParser.Create_trigger_stmtContext):
        pass


    # Enter a parse tree produced by SQLiteParser#create_view_stmt.
    def enterCreate_view_stmt(self, ctx:SQLiteParser.Create_view_stmtContext):
        pass

    # Exit a parse tree produced by SQLiteParser#create_view_stmt.
    def exitCreate_view_stmt(self, ctx:SQLiteParser.Create_view_stmtContext):
        pass


    # Enter a parse tree produced by SQLiteParser#create_virtual_table_stmt.
    def enterCreate_virtual_table_stmt(self, ctx:SQLiteParser.Create_virtual_table_stmtContext):
        pass

    # Exit a parse tree produced by SQLiteParser#create_virtual_table_stmt.
    def exitCreate_virtual_table_stmt(self, ctx:SQLiteParser.Create_virtual_table_stmtContext):
        pass


    # Enter a parse tree produced by SQLiteParser#delete_stmt.
    def enterDelete_stmt(self, ctx:SQLiteParser.Delete_stmtContext):
        pass

    # Exit a parse tree produced by SQLiteParser#delete_stmt.
    def exitDelete_stmt(self, ctx:SQLiteParser.Delete_stmtContext):
        pass


    # Enter a parse tree produced by SQLiteParser#delete_stmt_limited.
    def enterDelete_stmt_limited(self, ctx:SQLiteParser.Delete_stmt_limitedContext):
        pass

    # Exit a parse tree produced by SQLiteParser#delete_stmt_limited.
    def exitDelete_stmt_limited(self, ctx:SQLiteParser.Delete_stmt_limitedContext):
        pass


    # Enter a parse tree produced by SQLiteParser#detach_stmt.
    def enterDetach_stmt(self, ctx:SQLiteParser.Detach_stmtContext):
        pass

    # Exit a parse tree produced by SQLiteParser#detach_stmt.
    def exitDetach_stmt(self, ctx:SQLiteParser.Detach_stmtContext):
        pass


    # Enter a parse tree produced by SQLiteParser#drop_index_stmt.
    def enterDrop_index_stmt(self, ctx:SQLiteParser.Drop_index_stmtContext):
        pass

    # Exit a parse tree produced by SQLiteParser#drop_index_stmt.
    def exitDrop_index_stmt(self, ctx:SQLiteParser.Drop_index_stmtContext):
        pass


    # Enter a parse tree produced by SQLiteParser#drop_table_stmt.
    def enterDrop_table_stmt(self, ctx:SQLiteParser.Drop_table_stmtContext):
        pass

    # Exit a parse tree produced by SQLiteParser#drop_table_stmt.
    def exitDrop_table_stmt(self, ctx:SQLiteParser.Drop_table_stmtContext):
        pass


    # Enter a parse tree produced by SQLiteParser#drop_trigger_stmt.
    def enterDrop_trigger_stmt(self, ctx:SQLiteParser.Drop_trigger_stmtContext):
        pass

    # Exit a parse tree produced by SQLiteParser#drop_trigger_stmt.
    def exitDrop_trigger_stmt(self, ctx:SQLiteParser.Drop_trigger_stmtContext):
        pass


    # Enter a parse tree produced by SQLiteParser#drop_view_stmt.
    def enterDrop_view_stmt(self, ctx:SQLiteParser.Drop_view_stmtContext):
        pass

    # Exit a parse tree produced by SQLiteParser#drop_view_stmt.
    def exitDrop_view_stmt(self, ctx:SQLiteParser.Drop_view_stmtContext):
        pass


    # Enter a parse tree produced by SQLiteParser#factored_select_stmt.
    def enterFactored_select_stmt(self, ctx:SQLiteParser.Factored_select_stmtContext):
        pass

    # Exit a parse tree produced by SQLiteParser#factored_select_stmt.
    def exitFactored_select_stmt(self, ctx:SQLiteParser.Factored_select_stmtContext):
        pass


    # Enter a parse tree produced by SQLiteParser#insert_stmt.
    def enterInsert_stmt(self, ctx:SQLiteParser.Insert_stmtContext):
        pass

    # Exit a parse tree produced by SQLiteParser#insert_stmt.
    def exitInsert_stmt(self, ctx:SQLiteParser.Insert_stmtContext):
        pass


    # Enter a parse tree produced by SQLiteParser#pragma_stmt.
    def enterPragma_stmt(self, ctx:SQLiteParser.Pragma_stmtContext):
        pass

    # Exit a parse tree produced by SQLiteParser#pragma_stmt.
    def exitPragma_stmt(self, ctx:SQLiteParser.Pragma_stmtContext):
        pass


    # Enter a parse tree produced by SQLiteParser#reindex_stmt.
    def enterReindex_stmt(self, ctx:SQLiteParser.Reindex_stmtContext):
        pass

    # Exit a parse tree produced by SQLiteParser#reindex_stmt.
    def exitReindex_stmt(self, ctx:SQLiteParser.Reindex_stmtContext):
        pass


    # Enter a parse tree produced by SQLiteParser#release_stmt.
    def enterRelease_stmt(self, ctx:SQLiteParser.Release_stmtContext):
        pass

    # Exit a parse tree produced by SQLiteParser#release_stmt.
    def exitRelease_stmt(self, ctx:SQLiteParser.Release_stmtContext):
        pass


    # Enter a parse tree produced by SQLiteParser#rollback_stmt.
    def enterRollback_stmt(self, ctx:SQLiteParser.Rollback_stmtContext):
        pass

    # Exit a parse tree produced by SQLiteParser#rollback_stmt.
    def exitRollback_stmt(self, ctx:SQLiteParser.Rollback_stmtContext):
        pass


    # Enter a parse tree produced by SQLiteParser#savepoint_stmt.
    def enterSavepoint_stmt(self, ctx:SQLiteParser.Savepoint_stmtContext):
        pass

    # Exit a parse tree produced by SQLiteParser#savepoint_stmt.
    def exitSavepoint_stmt(self, ctx:SQLiteParser.Savepoint_stmtContext):
        pass


    # Enter a parse tree produced by SQLiteParser#simple_select_stmt.
    def enterSimple_select_stmt(self, ctx:SQLiteParser.Simple_select_stmtContext):
        pass

    # Exit a parse tree produced by SQLiteParser#simple_select_stmt.
    def exitSimple_select_stmt(self, ctx:SQLiteParser.Simple_select_stmtContext):
        pass


    # Enter a parse tree produced by SQLiteParser#select_stmt.
    def enterSelect_stmt(self, ctx:SQLiteParser.Select_stmtContext):
        pass

    # Exit a parse tree produced by SQLiteParser#select_stmt.
    def exitSelect_stmt(self, ctx:SQLiteParser.Select_stmtContext):
        pass


    # Enter a parse tree produced by SQLiteParser#select_or_values.
    def enterSelect_or_values(self, ctx:SQLiteParser.Select_or_valuesContext):
        pass

    # Exit a parse tree produced by SQLiteParser#select_or_values.
    def exitSelect_or_values(self, ctx:SQLiteParser.Select_or_valuesContext):
        pass


    # Enter a parse tree produced by SQLiteParser#update_stmt.
    def enterUpdate_stmt(self, ctx:SQLiteParser.Update_stmtContext):
        pass

    # Exit a parse tree produced by SQLiteParser#update_stmt.
    def exitUpdate_stmt(self, ctx:SQLiteParser.Update_stmtContext):
        pass


    # Enter a parse tree produced by SQLiteParser#update_stmt_limited.
    def enterUpdate_stmt_limited(self, ctx:SQLiteParser.Update_stmt_limitedContext):
        pass

    # Exit a parse tree produced by SQLiteParser#update_stmt_limited.
    def exitUpdate_stmt_limited(self, ctx:SQLiteParser.Update_stmt_limitedContext):
        pass


    # Enter a parse tree produced by SQLiteParser#vacuum_stmt.
    def enterVacuum_stmt(self, ctx:SQLiteParser.Vacuum_stmtContext):
        pass

    # Exit a parse tree produced by SQLiteParser#vacuum_stmt.
    def exitVacuum_stmt(self, ctx:SQLiteParser.Vacuum_stmtContext):
        pass


    # Enter a parse tree produced by SQLiteParser#column_def.
    def enterColumn_def(self, ctx:SQLiteParser.Column_defContext):
        pass

    # Exit a parse tree produced by SQLiteParser#column_def.
    def exitColumn_def(self, ctx:SQLiteParser.Column_defContext):
        pass


    # Enter a parse tree produced by SQLiteParser#type_name.
    def enterType_name(self, ctx:SQLiteParser.Type_nameContext):
        pass

    # Exit a parse tree produced by SQLiteParser#type_name.
    def exitType_name(self, ctx:SQLiteParser.Type_nameContext):
        pass


    # Enter a parse tree produced by SQLiteParser#column_constraint.
    def enterColumn_constraint(self, ctx:SQLiteParser.Column_constraintContext):
        pass

    # Exit a parse tree produced by SQLiteParser#column_constraint.
    def exitColumn_constraint(self, ctx:SQLiteParser.Column_constraintContext):
        pass


    # Enter a parse tree produced by SQLiteParser#conflict_clause.
    def enterConflict_clause(self, ctx:SQLiteParser.Conflict_clauseContext):
        pass

    # Exit a parse tree produced by SQLiteParser#conflict_clause.
    def exitConflict_clause(self, ctx:SQLiteParser.Conflict_clauseContext):
        pass


    # Enter a parse tree produced by SQLiteParser#expr.
    def enterExpr(self, ctx:SQLiteParser.ExprContext):
        pass

    # Exit a parse tree produced by SQLiteParser#expr.
    def exitExpr(self, ctx:SQLiteParser.ExprContext):
        pass


    # Enter a parse tree produced by SQLiteParser#foreign_key_clause.
    def enterForeign_key_clause(self, ctx:SQLiteParser.Foreign_key_clauseContext):
        pass

    # Exit a parse tree produced by SQLiteParser#foreign_key_clause.
    def exitForeign_key_clause(self, ctx:SQLiteParser.Foreign_key_clauseContext):
        pass


    # Enter a parse tree produced by SQLiteParser#raise_function.
    def enterRaise_function(self, ctx:SQLiteParser.Raise_functionContext):
        pass

    # Exit a parse tree produced by SQLiteParser#raise_function.
    def exitRaise_function(self, ctx:SQLiteParser.Raise_functionContext):
        pass


    # Enter a parse tree produced by SQLiteParser#indexed_column.
    def enterIndexed_column(self, ctx:SQLiteParser.Indexed_columnContext):
        pass

    # Exit a parse tree produced by SQLiteParser#indexed_column.
    def exitIndexed_column(self, ctx:SQLiteParser.Indexed_columnContext):
        pass


    # Enter a parse tree produced by SQLiteParser#table_constraint.
    def enterTable_constraint(self, ctx:SQLiteParser.Table_constraintContext):
        pass

    # Exit a parse tree produced by SQLiteParser#table_constraint.
    def exitTable_constraint(self, ctx:SQLiteParser.Table_constraintContext):
        pass


    # Enter a parse tree produced by SQLiteParser#with_clause.
    def enterWith_clause(self, ctx:SQLiteParser.With_clauseContext):
        pass

    # Exit a parse tree produced by SQLiteParser#with_clause.
    def exitWith_clause(self, ctx:SQLiteParser.With_clauseContext):
        pass


    # Enter a parse tree produced by SQLiteParser#qualified_table_name.
    def enterQualified_table_name(self, ctx:SQLiteParser.Qualified_table_nameContext):
        pass

    # Exit a parse tree produced by SQLiteParser#qualified_table_name.
    def exitQualified_table_name(self, ctx:SQLiteParser.Qualified_table_nameContext):
        pass


    # Enter a parse tree produced by SQLiteParser#ordering_term.
    def enterOrdering_term(self, ctx:SQLiteParser.Ordering_termContext):
        pass

    # Exit a parse tree produced by SQLiteParser#ordering_term.
    def exitOrdering_term(self, ctx:SQLiteParser.Ordering_termContext):
        pass


    # Enter a parse tree produced by SQLiteParser#pragma_value.
    def enterPragma_value(self, ctx:SQLiteParser.Pragma_valueContext):
        pass

    # Exit a parse tree produced by SQLiteParser#pragma_value.
    def exitPragma_value(self, ctx:SQLiteParser.Pragma_valueContext):
        pass


    # Enter a parse tree produced by SQLiteParser#common_table_expression.
    def enterCommon_table_expression(self, ctx:SQLiteParser.Common_table_expressionContext):
        pass

    # Exit a parse tree produced by SQLiteParser#common_table_expression.
    def exitCommon_table_expression(self, ctx:SQLiteParser.Common_table_expressionContext):
        pass


    # Enter a parse tree produced by SQLiteParser#result_column.
    def enterResult_column(self, ctx:SQLiteParser.Result_columnContext):
        pass

    # Exit a parse tree produced by SQLiteParser#result_column.
    def exitResult_column(self, ctx:SQLiteParser.Result_columnContext):
        pass


    # Enter a parse tree produced by SQLiteParser#table_or_subquery.
    def enterTable_or_subquery(self, ctx:SQLiteParser.Table_or_subqueryContext):
        pass

    # Exit a parse tree produced by SQLiteParser#table_or_subquery.
    def exitTable_or_subquery(self, ctx:SQLiteParser.Table_or_subqueryContext):
        pass


    # Enter a parse tree produced by SQLiteParser#join_clause.
    def enterJoin_clause(self, ctx:SQLiteParser.Join_clauseContext):
        pass

    # Exit a parse tree produced by SQLiteParser#join_clause.
    def exitJoin_clause(self, ctx:SQLiteParser.Join_clauseContext):
        pass


    # Enter a parse tree produced by SQLiteParser#join_operator.
    def enterJoin_operator(self, ctx:SQLiteParser.Join_operatorContext):
        pass

    # Exit a parse tree produced by SQLiteParser#join_operator.
    def exitJoin_operator(self, ctx:SQLiteParser.Join_operatorContext):
        pass


    # Enter a parse tree produced by SQLiteParser#join_constraint.
    def enterJoin_constraint(self, ctx:SQLiteParser.Join_constraintContext):
        pass

    # Exit a parse tree produced by SQLiteParser#join_constraint.
    def exitJoin_constraint(self, ctx:SQLiteParser.Join_constraintContext):
        pass


    # Enter a parse tree produced by SQLiteParser#select_core.
    def enterSelect_core(self, ctx:SQLiteParser.Select_coreContext):
        pass

    # Exit a parse tree produced by SQLiteParser#select_core.
    def exitSelect_core(self, ctx:SQLiteParser.Select_coreContext):
        pass


    # Enter a parse tree produced by SQLiteParser#compound_operator.
    def enterCompound_operator(self, ctx:SQLiteParser.Compound_operatorContext):
        pass

    # Exit a parse tree produced by SQLiteParser#compound_operator.
    def exitCompound_operator(self, ctx:SQLiteParser.Compound_operatorContext):
        pass


    # Enter a parse tree produced by SQLiteParser#signed_number.
    def enterSigned_number(self, ctx:SQLiteParser.Signed_numberContext):
        pass

    # Exit a parse tree produced by SQLiteParser#signed_number.
    def exitSigned_number(self, ctx:SQLiteParser.Signed_numberContext):
        pass


    # Enter a parse tree produced by SQLiteParser#literal_value.
    def enterLiteral_value(self, ctx:SQLiteParser.Literal_valueContext):
        pass

    # Exit a parse tree produced by SQLiteParser#literal_value.
    def exitLiteral_value(self, ctx:SQLiteParser.Literal_valueContext):
        pass


    # Enter a parse tree produced by SQLiteParser#unary_operator.
    def enterUnary_operator(self, ctx:SQLiteParser.Unary_operatorContext):
        pass

    # Exit a parse tree produced by SQLiteParser#unary_operator.
    def exitUnary_operator(self, ctx:SQLiteParser.Unary_operatorContext):
        pass


    # Enter a parse tree produced by SQLiteParser#error_message.
    def enterError_message(self, ctx:SQLiteParser.Error_messageContext):
        pass

    # Exit a parse tree produced by SQLiteParser#error_message.
    def exitError_message(self, ctx:SQLiteParser.Error_messageContext):
        pass


    # Enter a parse tree produced by SQLiteParser#module_argument.
    def enterModule_argument(self, ctx:SQLiteParser.Module_argumentContext):
        pass

    # Exit a parse tree produced by SQLiteParser#module_argument.
    def exitModule_argument(self, ctx:SQLiteParser.Module_argumentContext):
        pass


    # Enter a parse tree produced by SQLiteParser#column_alias.
    def enterColumn_alias(self, ctx:SQLiteParser.Column_aliasContext):
        pass

    # Exit a parse tree produced by SQLiteParser#column_alias.
    def exitColumn_alias(self, ctx:SQLiteParser.Column_aliasContext):
        pass


    # Enter a parse tree produced by SQLiteParser#keyword.
    def enterKeyword(self, ctx:SQLiteParser.KeywordContext):
        pass

    # Exit a parse tree produced by SQLiteParser#keyword.
    def exitKeyword(self, ctx:SQLiteParser.KeywordContext):
        pass


    # Enter a parse tree produced by SQLiteParser#name.
    def enterName(self, ctx:SQLiteParser.NameContext):
        pass

    # Exit a parse tree produced by SQLiteParser#name.
    def exitName(self, ctx:SQLiteParser.NameContext):
        pass


    # Enter a parse tree produced by SQLiteParser#function_name.
    def enterFunction_name(self, ctx:SQLiteParser.Function_nameContext):
        pass

    # Exit a parse tree produced by SQLiteParser#function_name.
    def exitFunction_name(self, ctx:SQLiteParser.Function_nameContext):
        pass


    # Enter a parse tree produced by SQLiteParser#database_name.
    def enterDatabase_name(self, ctx:SQLiteParser.Database_nameContext):
        pass

    # Exit a parse tree produced by SQLiteParser#database_name.
    def exitDatabase_name(self, ctx:SQLiteParser.Database_nameContext):
        pass


    # Enter a parse tree produced by SQLiteParser#schema_name.
    def enterSchema_name(self, ctx:SQLiteParser.Schema_nameContext):
        pass

    # Exit a parse tree produced by SQLiteParser#schema_name.
    def exitSchema_name(self, ctx:SQLiteParser.Schema_nameContext):
        pass


    # Enter a parse tree produced by SQLiteParser#table_function_name.
    def enterTable_function_name(self, ctx:SQLiteParser.Table_function_nameContext):
        pass

    # Exit a parse tree produced by SQLiteParser#table_function_name.
    def exitTable_function_name(self, ctx:SQLiteParser.Table_function_nameContext):
        pass


    # Enter a parse tree produced by SQLiteParser#table_name.
    def enterTable_name(self, ctx:SQLiteParser.Table_nameContext):
        pass

    # Exit a parse tree produced by SQLiteParser#table_name.
    def exitTable_name(self, ctx:SQLiteParser.Table_nameContext):
        pass


    # Enter a parse tree produced by SQLiteParser#table_or_index_name.
    def enterTable_or_index_name(self, ctx:SQLiteParser.Table_or_index_nameContext):
        pass

    # Exit a parse tree produced by SQLiteParser#table_or_index_name.
    def exitTable_or_index_name(self, ctx:SQLiteParser.Table_or_index_nameContext):
        pass


    # Enter a parse tree produced by SQLiteParser#new_table_name.
    def enterNew_table_name(self, ctx:SQLiteParser.New_table_nameContext):
        pass

    # Exit a parse tree produced by SQLiteParser#new_table_name.
    def exitNew_table_name(self, ctx:SQLiteParser.New_table_nameContext):
        pass


    # Enter a parse tree produced by SQLiteParser#column_name.
    def enterColumn_name(self, ctx:SQLiteParser.Column_nameContext):
        pass

    # Exit a parse tree produced by SQLiteParser#column_name.
    def exitColumn_name(self, ctx:SQLiteParser.Column_nameContext):
        pass


    # Enter a parse tree produced by SQLiteParser#collation_name.
    def enterCollation_name(self, ctx:SQLiteParser.Collation_nameContext):
        pass

    # Exit a parse tree produced by SQLiteParser#collation_name.
    def exitCollation_name(self, ctx:SQLiteParser.Collation_nameContext):
        pass


    # Enter a parse tree produced by SQLiteParser#foreign_table.
    def enterForeign_table(self, ctx:SQLiteParser.Foreign_tableContext):
        pass

    # Exit a parse tree produced by SQLiteParser#foreign_table.
    def exitForeign_table(self, ctx:SQLiteParser.Foreign_tableContext):
        pass


    # Enter a parse tree produced by SQLiteParser#index_name.
    def enterIndex_name(self, ctx:SQLiteParser.Index_nameContext):
        pass

    # Exit a parse tree produced by SQLiteParser#index_name.
    def exitIndex_name(self, ctx:SQLiteParser.Index_nameContext):
        pass


    # Enter a parse tree produced by SQLiteParser#trigger_name.
    def enterTrigger_name(self, ctx:SQLiteParser.Trigger_nameContext):
        pass

    # Exit a parse tree produced by SQLiteParser#trigger_name.
    def exitTrigger_name(self, ctx:SQLiteParser.Trigger_nameContext):
        pass


    # Enter a parse tree produced by SQLiteParser#view_name.
    def enterView_name(self, ctx:SQLiteParser.View_nameContext):
        pass

    # Exit a parse tree produced by SQLiteParser#view_name.
    def exitView_name(self, ctx:SQLiteParser.View_nameContext):
        pass


    # Enter a parse tree produced by SQLiteParser#module_name.
    def enterModule_name(self, ctx:SQLiteParser.Module_nameContext):
        pass

    # Exit a parse tree produced by SQLiteParser#module_name.
    def exitModule_name(self, ctx:SQLiteParser.Module_nameContext):
        pass


    # Enter a parse tree produced by SQLiteParser#pragma_name.
    def enterPragma_name(self, ctx:SQLiteParser.Pragma_nameContext):
        pass

    # Exit a parse tree produced by SQLiteParser#pragma_name.
    def exitPragma_name(self, ctx:SQLiteParser.Pragma_nameContext):
        pass


    # Enter a parse tree produced by SQLiteParser#savepoint_name.
    def enterSavepoint_name(self, ctx:SQLiteParser.Savepoint_nameContext):
        pass

    # Exit a parse tree produced by SQLiteParser#savepoint_name.
    def exitSavepoint_name(self, ctx:SQLiteParser.Savepoint_nameContext):
        pass


    # Enter a parse tree produced by SQLiteParser#table_alias.
    def enterTable_alias(self, ctx:SQLiteParser.Table_aliasContext):
        pass

    # Exit a parse tree produced by SQLiteParser#table_alias.
    def exitTable_alias(self, ctx:SQLiteParser.Table_aliasContext):
        pass


    # Enter a parse tree produced by SQLiteParser#transaction_name.
    def enterTransaction_name(self, ctx:SQLiteParser.Transaction_nameContext):
        pass

    # Exit a parse tree produced by SQLiteParser#transaction_name.
    def exitTransaction_name(self, ctx:SQLiteParser.Transaction_nameContext):
        pass


    # Enter a parse tree produced by SQLiteParser#any_name.
    def enterAny_name(self, ctx:SQLiteParser.Any_nameContext):
        pass

    # Exit a parse tree produced by SQLiteParser#any_name.
    def exitAny_name(self, ctx:SQLiteParser.Any_nameContext):
        pass



del SQLiteParser