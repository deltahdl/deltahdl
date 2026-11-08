#include <gtest/gtest.h>

#include <string>

#include "fixture_simulator.h"

using namespace delta;

namespace {

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
