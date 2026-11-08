#include <gtest/gtest.h>

#include <cstdint>
#include <string>

#include "fixture_simulator.h"
#include "helpers_scheduler.h"

using namespace delta;

namespace {

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
         "    static C o = new;\n"
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

TEST(DistributionRun, ARangesWeightAppliesToItWholeUnderAnotherConstraint) {
  const std::string kSrc =
      Design("x > 101; x dist {[100:102] := 1, 103 := 1};", 400);
  EXPECT_EQ(RunAndGet(kSrc, "n100"), uint64_t{0});
  EXPECT_EQ(RunAndGet(kSrc, "n101"), uint64_t{0});
  EXPECT_EQ(RunAndGet(kSrc, "other"), uint64_t{0});
  EXPECT_GT(RunAndGet(kSrc, "n102"), 2 * RunAndGet(kSrc, "n103"));
}

TEST(DistributionRun, AWholeRangeWeightSurvivesAnotherConstraintToo) {
  const std::string kSrc =
      Design("x > 101; x dist {[100:102] :/ 3, 103 := 1};", 400);
  EXPECT_EQ(RunAndGet(kSrc, "n100"), uint64_t{0});
  EXPECT_EQ(RunAndGet(kSrc, "n101"), uint64_t{0});
  EXPECT_GT(RunAndGet(kSrc, "n102"), 2 * RunAndGet(kSrc, "n103"));
}

TEST(DistributionRun, AnExcludedValueLeavesTheOthersAtTheirWeights) {
  const std::string kSrc =
      Design("x != 200; x dist {100 := 1, 200 := 2, 300 := 5};", 256);
  EXPECT_EQ(RunAndGet(kSrc, "n200"), uint64_t{0});
  EXPECT_EQ(RunAndGet(kSrc, "other"), uint64_t{0});
  EXPECT_GT(RunAndGet(kSrc, "n100"), uint64_t{0});
  EXPECT_GT(RunAndGet(kSrc, "n300"), 2 * RunAndGet(kSrc, "n100"));
}

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
      "    static M m = new;\n"
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
      "    static M m = new;\n"
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

TEST(SetMembershipRun, AnArrayOperandContributesItsElements) {
  const std::string kSrc =
      "class C;\n"
      "  rand bit [7:0] x;\n"
      "  bit [7:0] allowed[4] = '{11, 22, 33, 44};\n"
      "  constraint c { x inside {allowed}; }\n"
      "endclass\n"
      "module t;\n"
      "  int bad = 0;\n"
      "  bit [3:0] seen = 0;\n"
      "  initial begin\n"
      "    static C c = new;\n"
      "    repeat (80) begin\n"
      "      if (c.randomize() != 1) bad++;\n"
      "      case (c.x)\n"
      "        11: seen[0] = 1; 22: seen[1] = 1;\n"
      "        33: seen[2] = 1; 44: seen[3] = 1;\n"
      "        default: bad++;\n"
      "      endcase\n"
      "    end\n"
      "  end\n"
      "endmodule\n";
  EXPECT_EQ(RunAndGet(kSrc, "bad"), uint64_t{0});
  EXPECT_EQ(RunAndGet(kSrc, "seen"), uint64_t{15});
}

TEST(SetMembershipRun, ARealInsideARealRangeIsDrawnWithinIt) {
  const std::string kSrc =
      "class C;\n"
      "  rand real a;\n"
      "  rand real b;\n"
      "  constraint ca { a dist { -100.0 := 5, [0.70:1.43] :/ 1 }; }\n"
      "  constraint cb { b inside {[3.30:3.65]}; }\n"
      "endclass\n"
      "module t;\n"
      "  int bad = 0;\n"
      "  initial begin\n"
      "    static C c = new;\n"
      "    repeat (50) begin\n"
      "      if (c.randomize() != 1) bad++;\n"
      "      if (!(c.a == -100.0 || (c.a >= 0.70 && c.a <= 1.43))) bad++;\n"
      "      if (!(c.b >= 3.30 && c.b <= 3.65)) bad++;\n"
      "    end\n"
      "  end\n"
      "endmodule\n";
  EXPECT_EQ(RunAndGet(kSrc, "bad"), uint64_t{0});
}

TEST(SetMembershipRun, ARealInsideASetOfValuesAndRangesTakesOne) {
  SimFixture f;
  std::string out = RunCapture(
      "class C; rand real b; constraint c { b inside {1.5, 2.5, [3.0:3.5]}; }\n"
      "endclass\n"
      "module t;\n"
      "  int bad = 0, ones = 0, twos = 0, ranged = 0;\n"
      "  initial begin\n"
      "    static C c = new;\n"
      "    repeat (60) begin\n"
      "      if (c.randomize() != 1) bad++;\n"
      "      if (c.b == 1.5) ones++;\n"
      "      else if (c.b == 2.5) twos++;\n"
      "      else if (c.b >= 3.0 && c.b <= 3.5) ranged++;\n"
      "      else bad++;\n"
      "    end\n"
      "    $display(\"%0d %0d\", bad, ones > 0 && twos > 0 && ranged > 0);\n"
      "  end\n"
      "endmodule\n",
      f);
  EXPECT_EQ(out, "0 1\n");
}

TEST(SetMembershipRun, ARealInsideAToleranceRangeIsDrawnWithinIt) {
  SimFixture f;
  std::string out = RunCapture(
      "class C;\n"
      "  rand real b;\n"
      "  constraint c { b inside {[2.0 +/- 0.25], [10.0 +%- 5.0]}; }\n"
      "endclass\n"
      "module t;\n"
      "  int bad = 0;\n"
      "  initial begin\n"
      "    static C c = new;\n"
      "    repeat (40) begin\n"
      "      if (c.randomize() != 1) bad++;\n"
      "      if (!((c.b >= 1.75 && c.b <= 2.25) ||\n"
      "            (c.b >= 9.5 && c.b <= 10.5))) bad++;\n"
      "    end\n"
      "    $display(\"%0d\", bad);\n"
      "  end\n"
      "endmodule\n",
      f);
  EXPECT_EQ(out, "0\n");
}

TEST(DistributionRun, AWeightIsItsWholeUnsignedValue) {
  SimFixture f;
  std::string out = RunCapture(
      "class C;\n"
      "  rand bit [1:0] x, y, z, w;\n"
      "  constraint cx { x dist { 1 := 64'h1_0000_0000, 2 := 1 }; }\n"
      "  constraint cy { y dist { 1 := 65'h1_0000_0000_0000_0000, 2 := 1 }; }\n"
      "  constraint cz { z dist { 1 := 65'd0, 2 := 65'd3 }; }\n"
      "  constraint cw { w dist { [0:2] := 64'hffff_ffff_ffff_ffff, 3 := 1 }; "
      "}\n"
      "endclass\n"
      "module t;\n"
      "  int xs = 0, ys = 0, zs = 0, ws = 0;\n"
      "  initial begin\n"
      "    static C c = new;\n"
      "    repeat (20) begin\n"
      "      void'(c.randomize());\n"
      "      if (c.x == 1) xs++;\n"
      "      if (c.y == 1) ys++;\n"
      "      if (c.z == 2) zs++;\n"
      "      if (c.w != 3) ws++;\n"
      "    end\n"
      "    $display(\"%0d %0d %0d %0d\", xs, ys, zs, ws);\n"
      "  end\n"
      "endmodule\n",
      f);
  EXPECT_EQ(out, "20 20 20 20\n");
}

}  // namespace
