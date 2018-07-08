package cosette.ast;

/**
 * Created by akcheung on 7/6/18.
 */
public class Column extends Expr
{
  protected Relation relation; // initially null until type resolution

  protected String table;
  protected String name;

  public Column (String table, String name)
  {
    this.table = table;
    this.name = name;
  }

  public Column (String name)
  {
    this(null, name);
  }

  @Override
  public String toString ()
  {
    return (table == null) ? name : table + "." + name;
  }
}
