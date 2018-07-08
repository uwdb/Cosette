package cosette.ast;

/**
 * Created by akcheung on 7/6/18.
 */
public class StringLiteral extends Literal
{
  protected String value;

  public StringLiteral (String value)
  {
    this.value = value;
  }

  @Override public String toString () { return value; }
}
