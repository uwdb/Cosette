package cosette.test;


import cosette.parser.Main;
import org.apache.commons.io.FileUtils;
import org.junit.Test;
import org.junit.runner.RunWith;
import org.junit.runners.Parameterized;

import java.io.File;
import java.io.IOException;
import java.nio.file.Files;
import java.nio.file.Path;
import java.nio.file.Paths;
import java.util.Arrays;
import java.util.List;
import java.util.stream.Collectors;
import java.util.stream.Stream;

import static org.junit.Assert.assertEquals;

/**
 * Created by akcheung on 7/9/18.
 */
@RunWith(Parameterized.class)
public class Harness
{
  protected Path benchmark;

  public Harness(Path benchmark)
  {
    this.benchmark = benchmark;
  }

  @Parameterized.Parameters(name = "Test {index}: {0}")
  public static List<Path> files() throws IOException
  {
    String casesFolder = "test/cases";

    System.out.println("running cases from: " + casesFolder + "\n");

    // get all files inside the cases folder that ends with .sql, but ignore those
    // that are contained inside the "expected" subdirectory
    try (Stream<Path> paths = Files.walk(Paths.get(casesFolder)))
    {
      return  paths.filter(currentProgram -> Files.isRegularFile(currentProgram) &&
              currentProgram.getFileName().toString().endsWith(".sql") &&
              !currentProgram.toString().contains("expected/"))
              .collect(Collectors.toList());
    }

    // comment the above try statement and use this to run individual test cases
		//return Arrays.asList(Paths.get("test/cases/cq1.sql"));
  }

  @Test
  public void runTest() throws Exception
  {
    System.out.println("running benchmark: " + this.benchmark);

    String actual = Main.testMain(FileUtils.readFileToString(benchmark.toFile(), "utf-8"));

    String testDir = benchmark.toString()
            .substring(0, benchmark.toString().lastIndexOf(File.separator)+1);
    String expectedDir = testDir + "expected/";

    // compare the outputs from the current directory and those in expected.

    // expected output is in expected/<benchmark name>
    File expectedF = new File(expectedDir + "/" +
                              benchmark.toString().substring(benchmark.toString().lastIndexOf(File.separator)+1));

    if (expectedF == null)
      throw new RuntimeException("Cannot find expected output for: " + this.benchmark);

    String expected = FileUtils.readFileToString(expectedF, "utf-8").replace("\r\n", "");

    // compare ignoring case is good enough
    assertEquals(expected.toLowerCase(), actual.toLowerCase());
  }
}