package cosette.ast;

import org.antlr.v4.runtime.misc.Pair;

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

  protected List<Pair<Expr, Boolean>> orders;

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

  public void orders (List<Pair<Expr, Boolean>> orders)
  {
    this.orders = orders;
  }

  public void limit (Expr limit)
  {
    this.limit = limit;
  }

  public void offset (Expr offset)
  {
    this.offset = offset;
  }

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

    if (orders != null)
    {
      sb.append(" ORDER BY ");
      for (int i = 0; i < orders.size(); ++i)
      {
        Pair<Expr, Boolean> o = orders.get(i);
        sb.append(o.a);
        if (o.b) // is descending?
          sb.append(" DESC"); // ascending by default

        if (i < orders.size() - 1)
          sb.append(", ");
      }
    }

    if (limit != null)
      sb.append(" LIMIT " + limit);

    if (offset != null)
      sb.append(" OFFSET " + offset);

    return sb.toString();
  }
}
