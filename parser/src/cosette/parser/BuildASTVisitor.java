package cosette.parser;

import cosette.ast.*;
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
public class BuildASTVisitor extends CosetteBaseVisitor<Typed>
{
  // line 235
  @Override
  public Query visitSimple_select_stmt(Simple_select_stmtContext ctx)
  {
    return (Query)visit(ctx.select_core());
  }

  // line 241
  @Override
  public Query visitSelect_stmt(Select_stmtContext ctx)
  {
    return (Query)visit(ctx.select_or_values(0));
  }

  // line 248
  @Override
  public Query visitSelect_or_values(Select_or_valuesContext ctx)
  {
    return parseQuery(ctx.result_column(), ctx.table_or_subquery(), ctx.K_WHERE() == null, ctx.expr());
  }

  // line 325 -- parse Expr
  @Override
  public Expr visitUnaryExpr(UnaryExprContext ctx)
  {
     String op = ctx.op.getText();
     UnaryExpr.Op uop;
     if (op.equals("-")) uop = UnaryExpr.Op.NEG;
     else if (op.equals("+")) uop = UnaryExpr.Op.POS;
     else if (op.equals("~")) uop = UnaryExpr.Op.BITNOT;
     else if (op.equals(K_NOT)) uop = UnaryExpr.Op.NOT;
     else if (op.equals(K_ISNULL)) uop = UnaryExpr.Op.ISNULL;
     else if (op.equals(K_NOTNULL)) uop = UnaryExpr.Op.ISNOTNULL;
     else if (op.equals(K_NULL)) uop = UnaryExpr.Op.ISNOTNULL;
     else throw new ParseCancellationException("NYI: " + ctx.getText());

     return new UnaryExpr(uop, (Expr)visit(ctx.expr()));
  }

  @Override
  public Expr visitBinaryExpr(BinaryExprContext ctx)
  {
    String op = ctx.op.getText();
    BinaryExpr.Op binop;

    if (op.equals("||")) binop = BinaryExpr.Op.OR;
    else if (op.equals("*")) binop = BinaryExpr.Op.MULT;
    else if (op.equals("/")) binop = BinaryExpr.Op.DIV;
    else if (op.equals("%")) binop = BinaryExpr.Op.MOD;
    else if (op.equals("+")) binop = BinaryExpr.Op.ADD;
    else if (op.equals("-")) binop = BinaryExpr.Op.SUB;
    else if (op.equals("<<")) binop = BinaryExpr.Op.SHL;
    else if (op.equals(">>")) binop = BinaryExpr.Op.SHR;
    else if (op.equals("&")) binop = BinaryExpr.Op.BITAND;
    else if (op.equals("|")) binop = BinaryExpr.Op.BITOR;
    else if (op.equals("<")) binop = BinaryExpr.Op.LT;
    else if (op.equals("<=")) binop = BinaryExpr.Op.LE;
    else if (op.equals(">")) binop = BinaryExpr.Op.GT;
    else if (op.equals(">=")) binop = BinaryExpr.Op.GE;
    else if (op.equals("=")) binop = BinaryExpr.Op.EQ;
    else if (op.equals("==")) binop = BinaryExpr.Op.EQ;
    else if (op.equals("!=")) binop = BinaryExpr.Op.NEQ;
    else if (op.equals("<>")) binop = BinaryExpr.Op.NEQ;
    else if (op.equals(K_IS)) binop = BinaryExpr.Op.IS;
    else if (op.equals(K_NOT)) binop = BinaryExpr.Op.ISNOT; // it's really IS NOT

    else if (op.equals(K_IN))
      return new InExpr((Expr)visit(ctx.expr().get(0)), Collections.singletonList((Expr)visit(ctx.expr().get(1))), false);

    else if (op.equals(K_LIKE)) throw new ParseCancellationException("NYI: " + ctx.getText());
    else if (op.equals(K_AND)) binop = BinaryExpr.Op.AND;
    else if (op.equals(K_OR)) binop = BinaryExpr.Op.OR;
    else throw new ParseCancellationException("NYI: " + ctx.getText());

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
    Expr caseExpr = (ctx.K_CASE() != null) ? (Expr)visit(ctx.expr().get(0)) : null;
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

  // line 455
  @Override
  public Query visitSelect_core(Select_coreContext ctx)
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