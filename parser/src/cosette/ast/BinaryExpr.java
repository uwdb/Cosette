package cosette.ast;

/**
 * Created by akcheung on 7/6/18.
 */
public class BinaryExpr extends Typed implements Expr
{
  protected Expr left;
  protected Op op;
  protected Expr right;

  enum Op
  {
    OR("||"), MULT("*"), DIV("/"), MOD("%"), ADD("+"), SUB("-"), SHL("<<"), SHR(">>"),
    BITAND("&"), BITOR("|"), LT("<"), LE("<="), GT(">"), GE(">="), EQ("="), NEQ("<>"),
    IS("IS"), ISNOT("IS NOT"), LIKE("LIKE"),
    AND("AND");

    private String symbol;

    Op (String symbol) { this.symbol = symbol; }
    @Override public String toString () { return symbol; }
  }
}