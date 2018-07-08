package cosette.ast;

import java.util.List;

/**
 * Created by akcheung on 7/6/18.
 */
public class CaseExpr extends Expr
{
  protected Expr caseExpr;
  protected List<Expr> when;
  protected List<Expr> then;
  protected Expr elseExpr;

  public CaseExpr (Expr caseExpr, List<Expr> when, List<Expr> then, Expr elseExpr)
  {
    this.caseExpr = caseExpr;
    this.when = when;
    this.then = then;
    this.elseExpr = elseExpr;
  }

  @Override
  public String toString ()
  {
    StringBuffer sb = new StringBuffer();
    if (caseExpr != null)
      sb.append("CASE " + caseExpr);

    for (int i = 0; i < when.size(); ++i)
      sb.append(" WHEN " + when.get(i) + " THEN " + then.get(i));

    if (elseExpr != null)
      sb.append(" ELSE " + elseExpr);

    return sb.toString();
  }
}
