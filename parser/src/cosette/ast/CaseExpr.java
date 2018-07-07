package cosette.ast;

import java.util.List;

/**
 * Created by akcheung on 7/6/18.
 */
public class CaseExpr extends Typed implements Expr
{
  protected Expr caseExpr;
  protected List<Expr> when;
  protected List<Expr> then;
  protected Expr elseExpr;

}
