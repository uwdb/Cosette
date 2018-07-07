package cosette.ast;

/**
 * Created by akcheung on 7/6/18.
 */
public class DatetimeLiteral extends Typed implements Literal
{
  protected Kind kind;

  enum Kind
  {
    CurrentTime("CURRENT TIME"), CurrentDate("CURRENT DATE"), CurrentTimestamp("CURRENT TIMESTAMP");

    private String symbol;

    Kind (String symbol) { this.symbol = symbol; }
    @Override public String toString () { return symbol; }
  }

  public DatetimeLiteral (Kind kind) { this.kind = kind; }
  public Kind kind () { return kind; }
}
