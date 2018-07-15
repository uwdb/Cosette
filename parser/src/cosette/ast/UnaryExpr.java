package cosette.ast;

import org.antlr.v4.runtime.misc.ParseCancellationException;

/**
 * Created by akcheung on 7/6/18.
 */
public class UnaryExpr extends Expr
{
  protected Expr base;
  protected Op op;

  public enum Op
  {
    NEG("-"), POS("+"), BITNOT("~"), NOT("NOT"), ISNULL("IS NULL"), ISNOTNULL("IS NOT NULL");

    private String symbol;

    Op (String symbol) { this.symbol = symbol; }
    @Override public String toString () { return symbol; }
  }

  public UnaryExpr (Op op, Expr base)
  {
    this.op = op;
    this.base = base;
  }

  @Override public String toString ()
  {
    if (op == Op.NEG || op == Op.POS || op == Op.BITNOT)
      return op + "" + base;
    else if (op == Op.NOT)
      return op + " " + base;
    else if (op == Op.ISNULL || op == Op.ISNOTNULL)
      return base + " " + op;
    else
      throw new ParseCancellationException("NYI: " + op);
  }
}
