package cosette.ast;

import java.util.List;
import java.util.stream.Collectors;

/**
 * Created by akcheung on 7/6/18.
 *
 * According to the grammar IN can take either a query, list of Exprs, or a base table on the rhs
 */
public class InExpr extends Expr
{
  protected Expr left;

  // only one of {query, table, exprs} will be set
  protected Query query;
  protected Relation relation; // this will be set after type resolution, if table is set
  protected String table;
  protected List<Expr> exprs;

  protected boolean hasNot;

  public InExpr (Expr left, Query query, boolean hasNot)
  {
    this.left = left;
    this.query = query;
    this.relation = null;
    this.table = null;
    this.exprs = null;
    this.hasNot = hasNot;
  }

  public InExpr (Expr left, String table, boolean hasNot)
  {
    this.left = left;
    this.query = null;
    this.relation = null;
    this.table = table;
    this.exprs = null;
    this.hasNot = hasNot;
  }

  public InExpr (Expr left, List<Expr> exprs, boolean hasNot)
  {
    this.left = left;
    this.query = null;
    this.relation = null;
    this.table = null;
    this.exprs = exprs;
    this.hasNot = hasNot;
  }

  @Override
  public String toString ()
  {
    StringBuffer sb = new StringBuffer();
    sb.append(left);

    System.out.println("table: " + table + " query " + query);

    if (hasNot)
      sb.append(" NOT IN ");
    else
      sb.append(" IN ");

    if (query != null)
      sb.append("(" + query + ")");
    else if (exprs != null)
      sb.append("(" + String.join(", ", exprs.stream().map(e -> e.toString()).collect(Collectors.toList())) + ")");
    else if (table != null)
    {
      System.out.println("table is: " + table);
      sb.append(table);
    }

    return sb.toString();
  }
}
