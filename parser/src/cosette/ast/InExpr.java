package cosette.ast;

import java.util.List;

/**
 * Created by akcheung on 7/6/18.
 */
public class InExpr extends Typed implements Expr
{
  protected Relation relation;
  protected List<Expr> expr; // only one of them will be set
  protected boolean isRelation;


}
