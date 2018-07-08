package cosette.ast;

/**
 * Created by akcheung on 7/6/18.
 */
public class ExistsExpr extends Expr
{
  protected Expr expr;

  public ExistsExpr (Expr expr)
  {
    this.expr = expr;
  }

  @Override public String toString () { return "EXISTS " + expr; }
}
