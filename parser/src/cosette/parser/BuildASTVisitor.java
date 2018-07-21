package cosette.parser;

import cosette.ast.*;
import org.antlr.v4.runtime.misc.Pair;
import org.antlr.v4.runtime.misc.ParseCancellationException;
import org.antlr.v4.runtime.tree.TerminalNode;

import java.util.ArrayList;
import java.util.Collections;
import java.util.List;
import java.util.stream.Collectors;

import static cosette.parser.CosetteParser.*;

/**
 * Created by akcheung on 7/6/18.
 */
public class BuildASTVisitor extends CosetteBaseVisitor<Object>
{
  // line 41
  @Override
  public Query visitParse(ParseContext ctx)
  {
    return (Query)visit(ctx.sql_stmt());
  }

  // line 57
  @Override
  public Query visitSql_stmt(Sql_stmtContext ctx)
  {
    if (ctx.factored_select_stmt() != null)
      return (Query)visit(ctx.factored_select_stmt());

    else if (ctx.simple_select_stmt() != null)
      return (Query)visit(ctx.simple_select_stmt());

    else
      throw new ParseCancellationException("NYI: " + ctx.getText());
  }

  // line 191
  @Override
  public Query visitFactored_select_stmt(Factored_select_stmtContext ctx)
  {
    // XXX: parse the rest of select cores and CTEs
    if (ctx.select_core() != null && ctx.select_core().size() == 1)
    {
      Query q = (Query)visit(ctx.select_core(0));
      parseOrderLimitOffset(ctx.ordering_term(), ctx.K_LIMIT() != null, ctx.K_OFFSET() != null, ctx.expr(), q);
      return q;
    }
    else
      throw new ParseCancellationException("NYI: " + ctx.getText());
  }

  // line 236
  @Override
  public Query visitSimple_select_stmt(Simple_select_stmtContext ctx)
  {
    // XXX: parse the rest of select cores and CTEs
    Query q = (Query)visit(ctx.select_core());
    parseOrderLimitOffset(ctx.ordering_term(), ctx.K_LIMIT() != null, ctx.K_OFFSET() != null, ctx.expr(), q);
    return q;
  }

  // line 243
  @Override
  public Query visitSelect_stmt(Select_stmtContext ctx)
  {
    // XXX: parse the rest of select cores and CTEs
    Query q = (Query)visit(ctx.select_core(0));
    parseOrderLimitOffset(ctx.ordering_term(), ctx.K_LIMIT() != null, ctx.K_OFFSET() != null, ctx.expr(), q);
    return q;
  }

  // line 329 -- parse Expr
  @Override
  public Expr visitUnaryExpr(UnaryExprContext ctx)
  {
     String opStr = ctx.op.getText();
     UnaryExpr.Op uop = null;

     if (opStr.equals("-")) uop = UnaryExpr.Op.NEG;
     else if (opStr.equals("+")) uop = UnaryExpr.Op.POS;
     else if (opStr.equals("~")) uop = UnaryExpr.Op.BITNOT;

     int op = ctx.op.getType();
     switch(op)
     {
     case K_NOT: { uop = UnaryExpr.Op.NOT; break; }
     case K_ISNULL: { uop = UnaryExpr.Op.ISNULL; break; }
     case K_NOTNULL: { uop = UnaryExpr.Op.ISNOTNULL; break; }
     case K_NULL: { uop = UnaryExpr.Op.ISNOTNULL; break; }
     }

    if (uop == null)
      throw new ParseCancellationException("NYI: " + ctx.getText());

    return new UnaryExpr(uop, (Expr)visit(ctx.expr()));
  }

  @Override
  public Expr visitBinaryExpr(BinaryExprContext ctx)
  {
    String opStr = ctx.op.getText();
    BinaryExpr.Op binop = null;

    if (opStr.equals("||")) binop = BinaryExpr.Op.OR;
    else if (opStr.equals("*")) binop = BinaryExpr.Op.MULT;
    else if (opStr.equals("/")) binop = BinaryExpr.Op.DIV;
    else if (opStr.equals("%")) binop = BinaryExpr.Op.MOD;
    else if (opStr.equals("+")) binop = BinaryExpr.Op.ADD;
    else if (opStr.equals("-")) binop = BinaryExpr.Op.SUB;
    else if (opStr.equals("<<")) binop = BinaryExpr.Op.SHL;
    else if (opStr.equals(">>")) binop = BinaryExpr.Op.SHR;
    else if (opStr.equals("&")) binop = BinaryExpr.Op.BITAND;
    else if (opStr.equals("|")) binop = BinaryExpr.Op.BITOR;
    else if (opStr.equals("<")) binop = BinaryExpr.Op.LT;
    else if (opStr.equals("<=")) binop = BinaryExpr.Op.LE;
    else if (opStr.equals(">")) binop = BinaryExpr.Op.GT;
    else if (opStr.equals(">=")) binop = BinaryExpr.Op.GE;
    else if (opStr.equals("=")) binop = BinaryExpr.Op.EQ;
    else if (opStr.equals("==")) binop = BinaryExpr.Op.EQ;
    else if (opStr.equals("!=")) binop = BinaryExpr.Op.NEQ;
    else if (opStr.equals("<>")) binop = BinaryExpr.Op.NEQ;


    int op = ctx.op.getType();

    switch (op)
    {
      case K_IS: { binop = BinaryExpr.Op.IS; break; }
      case K_NOT: { binop = BinaryExpr.Op.ISNOT; break; }// it's really IS NOT
      case K_IN:
        return new InExpr((Expr)visit(ctx.expr().get(0)), Collections.singletonList((Expr)visit(ctx.expr().get(1))), false);

      case K_LIKE: throw new ParseCancellationException("NYI: " + ctx.getText());

      case K_AND: { binop = BinaryExpr.Op.AND; break; }
      case K_OR: { binop = BinaryExpr.Op.OR; break; }
    }

    if (binop == null) // not matched
      throw new ParseCancellationException("NYI: " + op + " in: " + ctx.getText() + " op " + op);

    return new BinaryExpr((Expr)visit(ctx.expr().get(0)), binop, (Expr)visit(ctx.expr().get(1)));
  }

  @Override
  public Column visitColumn(ColumnContext ctx)
  {
    if (ctx.table_name() != null)
      return new Column(ctx.table_name().getText(), ctx.column_name().getText());
    else
      return new Column(ctx.column_name().getText());
  }

  @Override
  public Expr visitInExpr(InExprContext ctx)
  {
    boolean hasNot = (ctx.K_NOT() != null);
    Expr e = (Expr)visit(ctx.expr().get(0));

    if (ctx.select_stmt() != null)
      return new InExpr(e, (Query)visit(ctx.select_stmt()), hasNot);
    else if (ctx.expr().size() > 1)
    {
      List<Expr> exprs = ctx.expr().subList(1, ctx.expr().size()).stream().map(ex -> (Expr)visit(ex)).collect(Collectors.toList());
      return new InExpr(e, exprs, hasNot);
    }
    else if (ctx.table_name() != null)
      return new InExpr(e, ctx.table_name().getText(), hasNot);
    else
      throw new ParseCancellationException("NYI: " + ctx.getText());
  }

  @Override
  public Expr visitExistsExpr(ExistsExprContext ctx)
  {
    boolean hasNot = (ctx.K_NOT() != null);
    boolean hasExists = (ctx.K_EXISTS() != null);

    Expr r;

    if (hasExists)
      r = new ExistsExpr(new ParenExpr((Query) visit(ctx.select_stmt())));
    else
      r = new ParenExpr((Query) visit(ctx.select_stmt()));

    if (hasNot)
      r = new UnaryExpr(UnaryExpr.Op.NOT, r);

    return r;
  }

  @Override
  public Expr visitCaseExpr(CaseExprContext ctx)
  {
    Expr caseExpr = (ctx.caseExpr != null) ? (Expr)visit(ctx.expr().get(0)) : null;
    Expr elseExpr = (ctx.K_ELSE() != null) ? (Expr)visit(ctx.expr().get(ctx.expr().size() - 1)) : null;

    List<Expr> when = new ArrayList<>();
    List<Expr> then = new ArrayList<>();
    int start = (caseExpr == null) ? 0 : 1;
    int end = (elseExpr == null) ? ctx.expr().size() : ctx.expr().size() - 1;
    for (int i = start; i < end; i += 2)
    {
      when.add((Expr)visit(ctx.expr().get(i)));
      then.add((Expr)visit(ctx.expr().get(i + 1)));
    }

    return new CaseExpr(caseExpr, when, then, elseExpr);
  }

  // line 414
  @Override
  public Pair<Expr, Boolean> visitOrdering_term(Ordering_termContext ctx)
  {
    Expr e = (Expr)visit(ctx.expr());
    boolean isDescending = (ctx.K_DESC() != null); // ascending default
    return new Pair<>(e, isDescending);
  }

  // line 425
  @Override
  public Column visitResult_column(Result_columnContext ctx)
  {
    if (ctx.getText().equals("*"))
      return new Column("*");
    else
      throw new ParseCancellationException("NYI: " + ctx.getText());
  }

  // line 431
  @Override
  public Relation visitTable_or_subquery(Table_or_subqueryContext ctx)
  {
    return new BaseTable(ctx.table_name().getText());
  }

  // line 459
  @Override
  public Query visitSelect_core(Select_coreContext ctx)
  {
    return parseQuery(ctx.result_column(), ctx.table_or_subquery(), ctx.K_WHERE() != null, ctx.expr());
  }

  protected Query parseQuery (List<Result_columnContext> cols, List<Table_or_subqueryContext> tables,
                              boolean hasWhere, List<CosetteParser.ExprContext> exprs)
  {
//    List<Column> select = new ArrayList<>();
//    for (Result_columnContext c : cols)
//      select.add((Column)visit(c));

    List<Column> select = cols.stream().map(c -> (Column)visit(c)).collect(Collectors.toList());

//    List<Relation> from = new ArrayList<>();
//    for (Table_or_subqueryContext c : tables)
//      from.add((Relation)visit(c));

    List<Relation> from = tables.stream().map(f -> (Relation)visit(f)).collect(Collectors.toList());

    Expr where = hasWhere ? (Expr)visit(exprs.get(0)) : null;

    return new Query(select, from, where);
  }

  protected void parseOrderLimitOffset (List<Ordering_termContext> orders, boolean hasLimit, boolean hasOffset,
                                        List<CosetteParser.ExprContext> exprs, Query q)
  {
    if (orders != null && orders.size() > 0)
    {
      List<Pair<Expr, Boolean>> o = orders.stream().map(x -> (Pair<Expr, Boolean>)visit(x)).collect(Collectors.toList());
      q.orders(o);
    }

    ExprContext limit = null;
    ExprContext offset = null;

    if (hasLimit)
    {
      if (hasOffset)
      {
        offset = exprs.get(exprs.size() - 1);
        limit = exprs.get(exprs.size() - 2);
      }
      else
        limit = exprs.get(exprs.size() - 1);
    }

    if (limit != null) q.limit((Expr)visit(limit));
    if (offset != null) q.offset((Expr)visit(offset));
  }

  // line 871
  @Override
  public Literal visitLiteral_value(Literal_valueContext ctx)
  {
    if (ctx.NUMERIC_LITERAL() != null)
      return new NumericLiteral(Long.parseLong(ctx.NUMERIC_LITERAL().getText()));
    else if (ctx.STRING_LITERAL() != null)
      return new StringLiteral(ctx.STRING_LITERAL().getText());
    else if (ctx.K_NULL() != null)
      return new Null();
    else if (ctx.K_CURRENT_TIME() != null)
      return new DatetimeLiteral(DatetimeLiteral.Kind.CurrentTime);
    else if (ctx.K_CURRENT_DATE() != null)
      return new DatetimeLiteral(DatetimeLiteral.Kind.CurrentDate);
    else if (ctx.K_CURRENT_TIMESTAMP() != null)
      return new DatetimeLiteral(DatetimeLiteral.Kind.CurrentTimestamp);
    else
      throw new ParseCancellationException("NYI: " + ctx.getText());
  }
}