#include <gtest/gtest.h>

#include <string>

#include "fixture_simulator.h"

using namespace delta;

namespace {

// 18.17: production lists separated by | are choices the generator makes at
// random and a list streams its items in sequence, so 200 runs of the
// clause's example reach each of add pop done, add push done, dec pop done
// and dec push done and nothing else, as the design
// test/src/e2e/randsequence_statement.sv runs it.
TEST(RandsequenceRun, TheClausesExampleReachesItsFourOutcomes) {
  SimFixture f;
  std::string out = RunCapture(
      "module t;\n"
      "  int i, f, s, d, seen[4], every = 1;\n"
      "  initial begin\n"
      "    for (i = 0; i < 4; i++) seen[i] = 0;\n"
      "    for (i = 0; i < 200; i++) begin\n"
      "      f = 0; s = 0; d = 0;\n"
      "      randsequence( main )\n"
      "        main   : first second done ;\n"
      "        first  : add | dec ;\n"
      "        second : pop | push ;\n"
      "        done   : { d = 1; } ;\n"
      "        add    : { f = 1; } ;\n"
      "        dec    : { f = 2; } ;\n"
      "        pop    : { s = 1; } ;\n"
      "        push   : { s = 2; } ;\n"
      "      endsequence\n"
      "      if (f == 1 && s == 1 && d == 1) seen[0] = 1;\n"
      "      else if (f == 1 && s == 2 && d == 1) seen[1] = 1;\n"
      "      else if (f == 2 && s == 1 && d == 1) seen[2] = 1;\n"
      "      else if (f == 2 && s == 2 && d == 1) seen[3] = 1;\n"
      "      else every = 0;\n"
      "    end\n"
      "    $display(\"%0d %0d %0d %0d %0d\", seen[0], seen[1], seen[2], "
      "seen[3], every);\n"
      "  end\n"
      "endmodule\n",
      f);
  EXPECT_EQ(out, "1 1 1 1 1\n");
}

// 18.17: the statement creates no loop of itself but a recursive production
// will loop, so a production naming itself as one alternative runs one or
// more times and stops; and the statement is an automatic scope whose code
// blocks are anonymous automatic scopes, a static variable needing the
// static prefix, so a static counter in a code block sees all three
// activations while an automatic one starts afresh each time, as the design
// test/src/e2e/randsequence_statement.sv runs it.
TEST(RandsequenceRun, ARecursiveProductionLoopsAndCodeBlockScopesAreAutomatic) {
  SimFixture f;
  std::string out = RunCapture(
      "module t;\n"
      "  int n = 0, sv, av, finite;\n"
      "  initial begin\n"
      "    randsequence( chain )\n"
      "      chain : { n++; } | { n++; } chain ;\n"
      "    endsequence\n"
      "    finite = n >= 1;\n"
      "    randsequence( main )\n"
      "      main  : count count count ;\n"
      "      count : { static int total = 0; int fresh = 0; total++; "
      "fresh++; sv = total; av = fresh; } ;\n"
      "    endsequence\n"
      "    $display(\"%0d %0d %0d\", finite, sv, av);\n"
      "  end\n"
      "endmodule\n",
      f);
  EXPECT_EQ(out, "1 3 1\n");
}

// 18.17: the production named in the parentheses is the top-level one and
// the first production is when none is named, so randsequence(second) runs
// only the second production and randsequence() starts at main, as the
// design test/src/e2e/randsequence_statement.sv runs it.
TEST(RandsequenceRun, TheNamedProductionOrElseTheFirstIsTheTopLevel) {
  SimFixture f;
  std::string out = RunCapture(
      "module t;\n"
      "  int f, s, d, only_second, from_first;\n"
      "  initial begin\n"
      "    f = 0; s = 0; d = 0;\n"
      "    randsequence( second )\n"
      "      main   : first second done ;\n"
      "      first  : { f = 1; } ;\n"
      "      second : { s = 1; } ;\n"
      "      done   : { d = 1; } ;\n"
      "    endsequence\n"
      "    only_second = f == 0 && s == 1 && d == 0;\n"
      "    f = 0; s = 0; d = 0;\n"
      "    randsequence()\n"
      "      main   : first second done ;\n"
      "      first  : { f = 1; } ;\n"
      "      second : { s = 1; } ;\n"
      "      done   : { d = 1; } ;\n"
      "    endsequence\n"
      "    from_first = f == 1 && s == 1 && d == 1;\n"
      "    $display(\"%0d %0d\", only_second, from_first);\n"
      "  end\n"
      "endmodule\n",
      f);
  EXPECT_EQ(out, "1 1\n");
}

// 18.17 with 13.4: a randsequence is a statement a function body may hold,
// and it generates its sequence there as it does in a process. The function's
// own variable is what the code blocks write, so the value the function
// returns is the sum the three productions left in it -- 6 -- and not the 0 a
// body that stepped over the statement returns. This is the shape of sv-tests'
// 18.17--random-sequence-generation-randsequence_0.sv.
TEST(RandsequenceRun, ARandsequenceInAFunctionBodyGeneratesItsSequence) {
  SimFixture f;
  std::string out = RunCapture(
      "function int F();\n"
      "  int x;\n"
      "  randsequence( main )\n"
      "    main : first second done;\n"
      "    first : { x = x + 1; };\n"
      "    second : { x = x + 2; };\n"
      "    done : { x = x + 3; };\n"
      "  endsequence\n"
      "  return x;\n"
      "endfunction\n"
      "module t;\n"
      "  initial $display(\"%0d\", F());\n"
      "endmodule\n",
      f);
  EXPECT_EQ(out, "6\n");
}

// 18.17.6: a return in a production code block ends that production and the
// sequence goes on, whatever encloses the randsequence. In a function body the
// return has a second candidate to end, the function itself, and it does not:
// `second` returns before its own addition, `third` still runs, and the
// function's own return hands out 25. A return that left the function would
// hand out 20 -- or, read as the function's, would want a value the bare
// return does not carry. This is the shape of sv-tests'
// 18.17.6--aborting-productions-break-and-return_2.sv.
TEST(RandsequenceRun, AReturnInAProductionInAFunctionEndsTheProductionOnly) {
  SimFixture f;
  std::string out = RunCapture(
      "function int F();\n"
      "  int x;\n"
      "  static int return_on = 1;\n"
      "  randsequence( main )\n"
      "    main : first second third;\n"
      "    first : { x = x + 20; };\n"
      "    second : { if (return_on == 1) return; x = x + 10; };\n"
      "    third : { x = x + 5; };\n"
      "  endsequence\n"
      "  return x;\n"
      "endfunction\n"
      "module t;\n"
      "  initial $display(\"%0d\", F());\n"
      "endmodule\n",
      f);
  EXPECT_EQ(out, "25\n");
}

}  // namespace
