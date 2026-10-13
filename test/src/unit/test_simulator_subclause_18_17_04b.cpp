#include <gtest/gtest.h>

#include <string>

#include "fixture_simulator.h"
#include "helpers_reported_error.h"

using namespace delta;

namespace {

// 18.17.4: a repeat production is generated as many times as its expression's
// value says, so a hundred runs of the clause's repeat($urandom_range(2, 6))
// PUSH each push 2 to 6 times and reach both ends, repeat(0) generates nothing
// and repeat(1 + 2) three, as the design test/src/e2e/repeat_production.sv runs
// it.
TEST(RepeatProductionRun, TheExpressionCountsTheGenerations) {
  SimFixture f;
  std::string out = RunCapture(
      "module t;\n"
      "  int i, count, in_range = 1, two_seen = 0, six_seen = 0;\n"
      "  int both_seen, zero_none, three;\n"
      "  initial begin\n"
      "    for (i = 0; i < 100; i++) begin\n"
      "      count = 0;\n"
      "      randsequence()\n"
      "        PUSH_OPER : repeat($urandom_range(2, 6)) PUSH ;\n"
      "        PUSH      : { count++; } ;\n"
      "      endsequence\n"
      "      if (count < 2 || count > 6) in_range = 0;\n"
      "      if (count == 2) two_seen = 1;\n"
      "      if (count == 6) six_seen = 1;\n"
      "    end\n"
      "    both_seen = two_seen && six_seen;\n"
      "    count = 0;\n"
      "    randsequence()\n"
      "      NONE : repeat(0) PUSH ;\n"
      "      PUSH : { count++; } ;\n"
      "    endsequence\n"
      "    zero_none = count == 0;\n"
      "    count = 0;\n"
      "    randsequence()\n"
      "      SOME : repeat(1 + 2) PUSH ;\n"
      "      PUSH : { count++; } ;\n"
      "    endsequence\n"
      "    three = count == 3;\n"
      "    $display(\"%0d %0d %0d %0d\", in_range, both_seen, zero_none, "
      "three);\n"
      "  end\n"
      "endmodule\n",
      f);
  EXPECT_EQ(out, "1 1 1 1\n");
}

// 18.17.4: nothing ends a repeat early except a break, and a break in the
// repeated production ends the whole randsequence block, so a break in the
// third of five pushes leaves three pushes and the production after the repeat
// ungenerated, as the design test/src/e2e/repeat_production.sv runs it.
TEST(RepeatProductionRun, ABreakInTheRepeatedProductionEndsTheWholeBlock) {
  SimFixture f;
  std::string out = RunCapture(
      "module t;\n"
      "  int count = 0, tail = 0, no_tail;\n"
      "  initial begin\n"
      "    randsequence()\n"
      "      main      : PUSH_OPER TAIL ;\n"
      "      PUSH_OPER : repeat(5) PUSH ;\n"
      "      PUSH      : { count++; if (count == 3) break; } ;\n"
      "      TAIL      : { tail = 1; } ;\n"
      "    endsequence\n"
      "    no_tail = tail == 0;\n"
      "    $display(\"%0d %0d\", count, no_tail);\n"
      "  end\n"
      "endmodule\n",
      f);
  EXPECT_EQ(out, "3 1\n");
}

// 18.17.4: the repeat expression shall come out as a non-negative integral
// value, so a negative count, -1 held in a signed int, is reported, and the
// production is generated no times rather than some 2^64 times.
TEST(RepeatProductionRun, ANegativeCountIsReportedAndGeneratesNothing) {
  SimFixture f;
  std::string out = RunCapture(
      "module t;\n"
      "  int n = -1, k = 0;\n"
      "  initial begin\n"
      "    randsequence (main)\n"
      "      main : repeat (n) tick ;\n"
      "      tick : { k++; } ;\n"
      "    endsequence\n"
      "    $display(\"%0d\", k);\n"
      "  end\n"
      "endmodule\n",
      f);
  EXPECT_EQ(out, "0\n");
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "randsequence repeat count is negative; a repeat "
                            "count needs a known integral value of zero or "
                            "more",
                            5, "18.17.4"));
}

// 18.17.4: a count with unknown bits is no integral value either, so it is
// reported, and the production is generated no times.
TEST(RepeatProductionRun, AnUnknownCountIsReportedAndGeneratesNothing) {
  SimFixture f;
  std::string out = RunCapture(
      "module t;\n"
      "  logic [3:0] n = 4'bx01x;\n"
      "  int k = 0;\n"
      "  initial begin\n"
      "    randsequence (main)\n"
      "      main : repeat (n) tick ;\n"
      "      tick : { k++; } ;\n"
      "    endsequence\n"
      "    $display(\"%0d\", k);\n"
      "  end\n"
      "endmodule\n",
      f);
  EXPECT_EQ(out, "0\n");
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "randsequence repeat count has unknown bits; a "
                            "repeat count needs a known integral value of "
                            "zero or more",
                            6, "18.17.4"));
}

}  // namespace
