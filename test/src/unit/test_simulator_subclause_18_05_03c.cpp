#include <gtest/gtest.h>

#include <sstream>
#include <string>
#include <vector>

#include "fixture_simulator.h"

using namespace delta;

namespace {

std::vector<int> Counts(const std::string& src) {
  SimFixture f;
  std::istringstream in(RunCapture(src, f));
  std::vector<int> counts;
  for (int n = 0; in >> n;) counts.push_back(n);
  return counts;
}

std::string Tally(const std::string& decl, const std::string& randomize,
                  const std::string& bins, const std::string& display) {
  return "class C;\n" + decl +
         "endclass\n"
         "module t;\n"
         "  int n0, n1, n2, n3, n4, rest;\n"
         "  initial begin\n"
         "    static C o = new;\n"
         "    repeat (800) begin\n"
         "      void'(" +
         randomize + ");\n" + bins +
         "    end\n"
         "    $display(" +
         display +
         ");\n"
         "  end\n"
         "endmodule\n";
}

const char* const kBins4 =
    "      if (o.x <= 2) n0++;\n"
    "      else if (o.x == 15) n1++;\n"
    "      else rest++;\n";

TEST(DistributionCases, ADefaultWeighsTheWholeRemainder) {
  const std::vector<int> kN =
      Counts(Tally("  rand bit [3:0] x;\n  constraint c { x dist {[0:2]:/3, "
                   "default:/1}; }\n",
                   "o.randomize()", kBins4, "\"%0d %0d %0d\", n0, n1, rest"));
  ASSERT_EQ(kN.size(), 3u);
  EXPECT_GT(kN[0], 500);
  EXPECT_LT(kN[0], 700);
}

TEST(DistributionCases, ADefaultOfZeroExcludesTheRemainder) {
  const std::vector<int> kN =
      Counts(Tally("  rand bit [3:0] x;\n  constraint c { x dist {[0:2]:/1, "
                   "default:/0}; }\n",
                   "o.randomize()", kBins4, "\"%0d %0d %0d\", n0, n1, rest"));
  ASSERT_EQ(kN.size(), 3u);
  EXPECT_EQ(kN[0], 800);
}

TEST(DistributionCases, ADefaultCoversTheSelfDeterminedTypesRemainder) {
  const std::vector<int> kN =
      Counts(Tally("  rand bit [3:0] x;\n  constraint c { x dist {[0:14]:=1, "
                   "default:/15}; }\n",
                   "o.randomize()", kBins4, "\"%0d %0d %0d\", n0, n1, rest"));
  ASSERT_EQ(kN.size(), 3u);
  EXPECT_GT(kN[1], 300);
  EXPECT_LT(kN[1], 500);
}

const char* const kBins100 =
    "      case (o.x)\n"
    "        100: n0++;\n"
    "        101: n1++;\n"
    "        102: n2++;\n"
    "        default: rest++;\n"
    "      endcase\n";
const char* const kShow3 = "\"%0d %0d %0d %0d\", n0, n1, n2, rest";

void ExpectOneTwoOne(const std::string& decl, const std::string& randomize) {
  const std::vector<int> kN = Counts(Tally(decl, randomize, kBins100, kShow3));
  ASSERT_EQ(kN.size(), 4u) << decl << randomize;
  EXPECT_EQ(kN[3], 0) << decl << randomize;
  EXPECT_GT(kN[1], 3 * kN[0] / 2) << decl << randomize;
  EXPECT_GT(kN[1], 3 * kN[2] / 2) << decl << randomize;
}

std::string RandX(const std::string& constraint) {
  return "  rand int x;\n  constraint c { x dist {" + constraint + "}; }\n";
}

TEST(DistributionCases, OverlappingItemsAddTheirWeights) {
  ExpectOneTwoOne(RandX("[100:102]:=1, 101:=1"), "o.randomize()");
  ExpectOneTwoOne(RandX("[100:101]:/1, [101:102]:/1"), "o.randomize()");
  ExpectOneTwoOne(RandX("100:/1, 101:/2, 102:/1"), "o.randomize()");
  ExpectOneTwoOne(RandX("100:/1, 101:/1, 101:/1, 102:/1"), "o.randomize()");
}

TEST(DistributionCases, OverlappingInlineItemsAddTheirWeights) {
  ExpectOneTwoOne("  rand int x;\n",
                  "o.randomize() with { x dist {[100:101]:/1, [101:102]:/1}; "
                  "}");
  ExpectOneTwoOne("  rand int x;\n",
                  "o.randomize() with { x dist {100:/1, 101:/2, 102:/1}; }");
}

void ExpectEven(const std::string& decl, const std::string& randomize) {
  const std::vector<int> kN = Counts(Tally(decl, randomize, kBins100, kShow3));
  ASSERT_EQ(kN.size(), 4u);
  EXPECT_EQ(kN[3], 0);
  for (int i = 0; i < 3; ++i) {
    EXPECT_GT(kN[i], 180) << i;
    EXPECT_LT(kN[i], 360) << i;
  }
}

TEST(DistributionCases, AZeroWeightCoveredByARangeLeavesTheValueEven) {
  ExpectEven(RandX("100:/0, [100:102]:/1"), "o.randomize()");
  ExpectEven("  rand int x;\n",
             "o.randomize() with { x dist {100:/0, [100:102]:/1}; }");
}

std::string Holds(const std::string& decls, const std::string& check,
                  const std::string& randomize = "o.randomize()") {
  return "class C;\n" + decls +
         "endclass\n"
         "module t;\n"
         "  int i, held = 0;\n"
         "  initial begin\n"
         "    static C o = new;\n"
         "    for (i = 0; i < 32; i++)\n"
         "      if (" +
         randomize + " && " + check +
         ") held++;\n"
         "    $display(\"%0d\", held);\n"
         "  end\n"
         "endmodule\n";
}

std::string RunHolds(const std::string& src) {
  SimFixture f;
  return RunCapture(src, f);
}

const char* const kMX =
    "  bit m = 1, n = 0;\n"
    "  rand bit [7:0] x;\n"
    "  rand int a, b;\n"
    "  rand bit [7:0] q[3];\n";

TEST(DistributionCases, DISABLED_ADistInAnIfBodyHolds) {
  EXPECT_EQ(RunHolds(Holds(std::string(kMX) +
                               "  constraint c { if (m) x dist {7 := 1}; }\n",
                           "o.x == 7")),
            "32\n");
}

TEST(DistributionCases, DISABLED_ADistInAnElseBodyHolds) {
  EXPECT_EQ(RunHolds(Holds(std::string(kMX) +
                               "  constraint c { if (n) x == 1; else x dist "
                               "{7 := 1}; }\n",
                           "o.x == 7")),
            "32\n");
}

TEST(DistributionCases, DISABLED_ADistInAnImplicationHolds) {
  EXPECT_EQ(RunHolds(Holds(
                std::string(kMX) + "  constraint c { m -> x dist {7 := 1}; }\n",
                "o.x == 7")),
            "32\n");
}

TEST(DistributionCases, DISABLED_ADistInAForeachBodyHolds) {
  EXPECT_EQ(
      RunHolds(Holds(std::string(kMX) +
                         "  constraint c { foreach (q[i]) q[i] dist {7 := 1}; "
                         "}\n",
                     "o.q[0] == 7 && o.q[1] == 7 && o.q[2] == 7")),
      "32\n");
}

TEST(DistributionCases, DISABLED_ADistOverASumHolds) {
  EXPECT_EQ(RunHolds(Holds(std::string(kMX) +
                               "  constraint c { a inside {[0:7]}; b inside "
                               "{[0:7]}; a + b dist {7 := 1}; }\n",
                           "o.a + o.b == 7")),
            "32\n");
}

TEST(DistributionCases, DISABLED_ADistInAScopeRandomizeBlockHolds) {
  SimFixture f;
  EXPECT_EQ(RunCapture("module t;\n"
                       "  bit [7:0] x;\n"
                       "  int i, held = 0;\n"
                       "  initial begin\n"
                       "    for (i = 0; i < 32; i++)\n"
                       "      if (std::randomize(x) with { x dist {7 := 1}; } "
                       "&& x == 7) held++;\n"
                       "    $display(\"%0d\", held);\n"
                       "  end\n"
                       "endmodule\n",
                       f),
            "32\n");
}

TEST(DistributionCases, AnInlineRangeWithAWholeWeightHolds) {
  EXPECT_EQ(RunHolds(Holds(kMX, "o.x inside {[3:4]}",
                           "o.randomize() with { x dist {[3:4] :/ 1}; }")),
            "32\n");
}

TEST(DistributionCases, DISABLED_NestedDistsHoldInAnExternalBlock) {
  EXPECT_EQ(
      RunHolds(
          "class C;\n" + std::string(kMX) +
          "  constraint c;\n"
          "endclass\n"
          "constraint C::c { if (m) x dist {7 := 1}; m -> a dist {3 := 1}; "
          "foreach (q[i]) q[i] dist {5 := 1}; }\n"
          "module t;\n"
          "  int i, held = 0;\n"
          "  initial begin\n"
          "    static C o = new;\n"
          "    for (i = 0; i < 32; i++)\n"
          "      if (o.randomize() && o.x == 7 && o.a == 3 && o.q[2] == 5) "
          "held++;\n"
          "    $display(\"%0d\", held);\n"
          "  end\n"
          "endmodule\n"),
      "32\n");
}

TEST(DistributionCases, DISABLED_NestedDistsHoldInAnInlineBlock) {
  EXPECT_EQ(
      RunHolds(Holds(kMX, "o.x == 7 && o.a == 3 && o.q[2] == 5",
                     "o.randomize() with { if (m) x dist {7 := 1}; m -> a "
                     "dist {3 := 1}; foreach (q[i]) q[i] dist {5 := 1}; }")),
      "32\n");
}

}  // namespace
