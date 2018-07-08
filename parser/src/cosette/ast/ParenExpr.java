package cosette.ast;

import org.antlr.v4.runtime.misc.ParseCancellationException;

/**
 * Created by akcheung on 7/8/18.
 *
 * An expression or a query that is encased by ( )s
 */
public class ParenExpr extends Expr
{
  protected Expr expr;
  protected Query query;

  public ParenExpr (Expr base)
  {
    this.expr = base;
    this.query = null;
  }

  public ParenExpr (Query base)
  {
    this.expr = null;
    this.query = base;
  }

  @Override public String toString ()
  {
    if (expr != null)
      return "(" + expr + ")";
    else if (query != null)
      return "(" + query + ")";
    else
      throw new ParseCancellationException("both expr and query are null in ParenExpr");
  }
}
