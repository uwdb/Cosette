package cosette.ast;

/**
 * Created by akcheung on 7/6/18.
 */
public abstract class Relation extends Typed
{
  protected String name;

  protected Relation (String name)
  {
    this.name = name;
  }

  public String name () { return name; }
}
