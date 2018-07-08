package cosette.ast;

import java.util.ArrayList;
import java.util.List;
import java.util.stream.Collectors;

/**
 * Created by akcheung on 7/6/18.
 */
public class Query extends Relation
{
  protected List<Column> select;
  protected List<Relation> from;
  protected Expr where;

  protected List<Expr> orderBy;
  protected List<Boolean> order;

  protected Expr limit;
  protected Expr offset;


  public Query (String name, List<Column> select, List<Relation> from, Expr where)
  {
    super(name);
    this.select = select;
    this.from  = from;
    this.where = where;
  }

  public Query (List<Column> select, List<Relation> from, Expr where)
  {
    super("");
    this.select = select;
    this.from  = from;
    this.where = where;
  }

  public String name () { return name; }

  @Override
  public String toString ()
  {
    StringBuffer sb = new StringBuffer();

    sb.append("SELECT ");
    List<String> cols = select.stream().map(c -> c.toString()).collect(Collectors.toList());
    sb.append(String.join(", ", cols));

    sb.append(" FROM ");
    List<String> tables = from.stream().map(t -> t.toString()).collect(Collectors.toList());
    sb.append(String.join(", ", tables));

    if (where != null)
      sb.append(" WHERE " + where.toString());

    return sb.toString();
  }
}
