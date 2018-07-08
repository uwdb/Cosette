package cosette.ast;

/**
 * Created by akcheung on 7/6/18.
 */
public class NumericLiteral extends Literal
{
  protected long value;

  public NumericLiteral (long value)
  {
    this.value = value;
  }

  @Override public String toString () { return "" + value; }
}
