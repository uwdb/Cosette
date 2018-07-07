package cosette.ast;

/**
 * Created by akcheung on 7/6/18.
 */
public class BaseTable extends Relation
{
  public BaseTable (String name)
  {
    super(name);
  }

  @Override public String toString () { return name; }
}
