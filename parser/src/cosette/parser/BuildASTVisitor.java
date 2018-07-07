package cosette.parser;

import cosette.ast.*;
import org.antlr.v4.runtime.misc.ParseCancellationException;
import org.antlr.v4.runtime.tree.TerminalNode;

import java.util.ArrayList;
import java.util.List;

/**
 * Created by akcheung on 7/6/18.
 */
public class BuildASTVisitor extends CosetteBaseVisitor<Typed>
{
  @Override
  public Query visitSimple_select_stmt(CosetteParser.Simple_select_stmtContext ctx)
  {
    return (Query)visit(ctx.select_core());
  }

  @Override
  public Query visitSelect_stmt(CosetteParser.Select_stmtContext ctx)
  {
    return (Query)visit(ctx.select_or_values(0));
  }

  @Override
  public Query visitSelect_or_values(CosetteParser.Select_or_valuesContext ctx)
  {
    return parseQuery(ctx.result_column(), ctx.table_or_subquery(), ctx.K_WHERE() == null, ctx.expr());
  }

  @Override
  public Query visitSelect_core(CosetteParser.Select_coreContext ctx)
  {
    return parseQuery(ctx.result_column(), ctx.table_or_subquery(), ctx.K_WHERE() == null, ctx.expr());
  }

  protected Query parseQuery (List<CosetteParser.Result_columnContext> cols,
                              List<CosetteParser.Table_or_subqueryContext> tables,
                              boolean hasWhere, List<CosetteParser.ExprContext> exprs)
  {
    List<Column> select = new ArrayList<>();
    for (CosetteParser.Result_columnContext c : cols)
      select.add((Column)visit(c));

    List<Relation> from = new ArrayList<>();
    for (CosetteParser.Table_or_subqueryContext c : tables)
      from.add((Relation)visit(c));

    Expr where = hasWhere ? null : (Expr)visit(exprs.get(0));

    return new Query(select, from, where);
  }

  @Override
  public Column visitResult_column(CosetteParser.Result_columnContext ctx)
  {
    if (ctx.getText().equals("*"))
      return new Column("*");
    else
      throw new ParseCancellationException("NYI: " + ctx.getText());
  }

  @Override
  public Relation visitTable_or_subquery(CosetteParser.Table_or_subqueryContext ctx)
  {
    return new BaseTable(ctx.table_name().getText());
  }
}