#include <gtest/gtest.h>

#include <cstdint>
#include <string>

#include "fixture_simulator.h"
#include "helpers_scheduler.h"

using namespace delta;

namespace {

// A class holding a rand int x under the constraint block `c`, randomized
// `draws` times by an initial that counts its draws as the design
// test/src/e2e/distribution_constraints.sv does, into the module's n100
// to n103, n200, n300 and other.
std::string Design(const std::string& constraint, int draws) {
  return "class C;\n"
         "  rand int x;\n"
         "  constraint c { " +
         constraint +
         " }\n"
         "endclass\n"
         "module t;\n"
         "  int n100, n101, n102, n103, n200, n300, other;\n"
         "  initial begin\n"
         "    C o = new;\n"
         "    repeat (" +
         std::to_string(draws) +
         ") begin\n"
         "      void'(o.randomize());\n"
         "      case (o.x)\n"
         "        100: n100++;\n"
         "        101: n101++;\n"
         "        102: n102++;\n"
         "        103: n103++;\n"
         "        200: n200++;\n"
         "        300: n300++;\n"
         "        default: other++;\n"
         "      endcase\n"
         "    end\n"
         "  end\n"
         "endmodule\n";
}

// §18.5.3: the weight of a range applies to the range as a whole, counting
// the values other constraints exclude from it: with x above 101, the range
// [100:102] weighted 3 leaves 102 three times as likely as 103.
TEST(DistributionRun, ARangesWeightAppliesToItWholeUnderAnotherConstraint) {
  const std::string kSrc =
      Design("x > 101; x dist {[100:102] := 1, 103 := 1};", 400);
  EXPECT_EQ(RunAndGet(kSrc, "n100"), uint64_t{0});
  EXPECT_EQ(RunAndGet(kSrc, "n101"), uint64_t{0});
  EXPECT_EQ(RunAndGet(kSrc, "other"), uint64_t{0});
  EXPECT_GT(RunAndGet(kSrc, "n102"), 2 * RunAndGet(kSrc, "n103"));
}

// §18.5.3: the same with the range weighted 3 as a whole by :/ -- the two
// spellings are equivalent, and the exclusion of 100 and 101 costs the range
// none of its weight either way.
TEST(DistributionRun, AWholeRangeWeightSurvivesAnotherConstraintToo) {
  const std::string kSrc =
      Design("x > 101; x dist {[100:102] :/ 3, 103 := 1};", 400);
  EXPECT_EQ(RunAndGet(kSrc, "n100"), uint64_t{0});
  EXPECT_EQ(RunAndGet(kSrc, "n101"), uint64_t{0});
  EXPECT_GT(RunAndGet(kSrc, "n102"), 2 * RunAndGet(kSrc, "n103"));
}

// §18.5.3: a constraint excluding a value of the set leaves the others at
// their weights, the clause's x != 200 leaving 100 and 300 at 1:5.
TEST(DistributionRun, AnExcludedValueLeavesTheOthersAtTheirWeights) {
  const std::string kSrc =
      Design("x != 200; x dist {100 := 1, 200 := 2, 300 := 5};", 256);
  EXPECT_EQ(RunAndGet(kSrc, "n200"), uint64_t{0});
  EXPECT_EQ(RunAndGet(kSrc, "other"), uint64_t{0});
  EXPECT_GT(RunAndGet(kSrc, "n100"), uint64_t{0});
  EXPECT_GT(RunAndGet(kSrc, "n300"), 2 * RunAndGet(kSrc, "n100"));
}

// §18.5.3: a distribution may mix real and integral values, a range of reals
// weighted as a whole with :/ and a tolerance range naming the reals within a
// percentage of its centre: every draw of a is -100 or within [0.70, 3.65],
// and the 13 of 20 on [3.30 +%- 1.0] outnumber the rest.
TEST(DistributionRun, ARealDistributionMixesRealAndIntegralItems) {
  SimFixture f;
  std::string out = RunCapture(
      "class M;\n"
      "  rand real a;\n"
      "  constraint c {\n"
      "    a dist { -100 := 5, [0.70:1.43] :/ 1, [3.30 +%- 1.0] :/ 13,\n"
      "             [1.43:3.65] :/ 1 };\n"
      "  }\n"
      "endclass\n"
      "module t;\n"
      "  int stated = 0, near = 0, rest = 0, other = 0;\n"
      "  initial begin\n"
      "    M m = new;\n"
      "    repeat (200) begin\n"
      "      void'(m.randomize());\n"
      "      if (m.a == -100.0) stated++;\n"
      "      else if (m.a >= 3.267 && m.a <= 3.333) near++;\n"
      "      else if (m.a >= 0.70 && m.a <= 3.65) rest++;\n"
      "      else other++;\n"
      "    end\n"
      "    $display(\"%0d %0d\", other == 0 && stated > 0 && rest > 0,\n"
      "             near > stated + rest);\n"
      "  end\n"
      "endmodule\n",
      f);
  EXPECT_EQ(out, "1 1\n");
}

// §18.5.3: a real variable's draw within a range item is admitted by the
// domain its relational constraints leave it, so a bound on the variable
// narrows the range without costing it its weight: with a below 1.0, the
// range [0.5:1.5] weighted 3 still outnumbers the value 0.25 weighted 1, and
// no draw reaches 1.0.
TEST(DistributionRun, ARealRangeKeepsItsWeightUnderABound) {
  SimFixture f;
  std::string out = RunCapture(
      "class M;\n"
      "  rand real a;\n"
      "  constraint c { a < 1.0; a dist { [0.5:1.5] :/ 3, 0.25 := 1 }; }\n"
      "endclass\n"
      "module t;\n"
      "  int low = 0, quarter = 0, other = 0;\n"
      "  initial begin\n"
      "    M m = new;\n"
      "    repeat (200) begin\n"
      "      void'(m.randomize());\n"
      "      if (m.a >= 0.5 && m.a < 1.0) low++;\n"
      "      else if (m.a == 0.25) quarter++;\n"
      "      else other++;\n"
      "    end\n"
      "    $display(\"%0d %0d %0d\", other, quarter > 0, low > 2 * quarter);\n"
      "  end\n"
      "endmodule\n",
      f);
  EXPECT_EQ(out, "0 1 1\n");
}

}  // namespace
