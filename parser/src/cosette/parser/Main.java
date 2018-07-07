package cosette.parser;

import cosette.ast.Typed;
import org.antlr.v4.runtime.*;
import org.antlr.v4.runtime.tree.ParseTree;
import org.antlr.v4.runtime.tree.ParseTreeWalker;

import java.util.ArrayList;
import java.util.List;

public class Main
{
  public static void main(String[] args) throws Exception
  {

    // The list that will hold our function names.
    final List<String> functionNames = new ArrayList<String>();

    // The select-statement to be parsed.
    String sql = "SELECT * from R";
    /*
    String sql = "SELECT log AS x FROM t1 \n" +
            "GROUP BY x\n" +
            "HAVING count(*) >= 4 \n" +
            "ORDER BY max(n) + 0";
            */

    // Create a lexer and parser for the input.
    CosetteLexer lexer = new CosetteLexer(CharStreams.fromString(sql));
    CosetteParser parser = new CosetteParser(new CommonTokenStream(lexer));

    parser.addErrorListener(new BaseErrorListener()
    {
      public void syntaxError(Recognizer<?,?> recognizer, Object offendingSymbol, int line,
                              int charPositionInLine, String msg, RecognitionException e)
      { throw new RuntimeException(e); }
    });

    // Invoke the `select_stmt` production.
    ParseTree tree = parser.select_stmt();

    // show tree in text form
    System.out.println("parse tree:" + tree.toStringTree(parser));

    Typed t = new BuildASTVisitor().visit(tree);

    System.out.println("got: " + t.toString());

    /*
    // Walk the `select_stmt` production and listen when the parser
    // enters the `expr` production.
    ParseTreeWalker.DEFAULT.walk(new cosette.parser.CosetteBaseListener()
    {

      @Override
      public void enterExpr(CosetteParser.ExprContext ctx)
      {
        // Check if the expression is a function call.
        if (ctx.function_name() != null)
        {
          // Yes, it was a function call: add the name of the function
          // to out list.
          functionNames.add(ctx.function_name().getText());
        }
      }
    }, tree);

    // Print the parsed functions.
    System.out.println("functionNames=" + functionNames);
    */
  }
}