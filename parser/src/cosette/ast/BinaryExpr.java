package cosette.ast;

/**
 * Created by akcheung on 7/6/18.
 */
public class BinaryExpr extends Expr
{
  protected Expr left;
  protected Op op;
  protected Expr right;

  public enum Op
  {
    OR("||"), MULT("*"), DIV("/"), MOD("%"), ADD("+"), SUB("-"), SHL("<<"), SHR(">>"),
    BITAND("&"), BITOR("|"), LT("<"), LE("<="), GT(">"), GE(">="), EQ("="), NEQ("<>"),
    IS("IS"), ISNOT("IS NOT"), LIKE("LIKE"),
    AND("AND");

    private String symbol;

    Op (String symbol) { this.symbol = symbol; }
    @Override public String toString () { return symbol; }
  }

  public BinaryExpr (Expr left, Op op, Expr right)
  {
    this.left = left;
    this.op = op;
    this.right = right;
  }

  @Override public String toString ()
  {
    return left + " " + op + " " + right;
  }
}