package cosette.ast;

/**
 * Created by akcheung on 7/6/18.
 */
public class UnaryExpr extends Typed implements Expr
{
  protected Expr base;
  protected Op op;

  enum Op
  {
    NEG("-"), POS("+"), BITNOT("~"), NOT("NOT"), ISNULL("IS NULL");

    private String symbol;

    Op (String symbol) { this.symbol = symbol; }
    @Override public String toString () { return symbol; }
  }
}
