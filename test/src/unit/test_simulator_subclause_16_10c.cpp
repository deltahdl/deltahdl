#include <gtest/gtest.h>

#include <cstddef>
#include <cstdint>
#include <string>
#include <vector>

#include "fixture_simulator.h"
#include "helpers_sequence_covers.h"
#include "helpers_sequence_ticks.h"

using namespace delta;

namespace {

struct ThreadCase {
  std::string body;
  uint64_t matches;
};

std::string ThreadDrive() { return DriveTicks({{1, 6}}); }

std::string ThreadSource(const std::vector<ThreadCase>& cases,
                         const std::string& extra = "") {
  std::string items = extra;
  for (size_t i = 0; i < cases.size(); ++i) {
    std::string n = std::to_string(i + 1);
    items += "  sequence s";
    items += n;
    items += "; int x, y;\n    @(posedge clk) ";
    items += cases[i].body;
    items += ";\n  endsequence\n  c";
    items += n;
    items += ": cover sequence (s";
    items += n;
    items += ");\n";
  }
  return SequenceCoverSource(items, ThreadDrive());
}

void ExpectThreadCounts(const std::vector<ThreadCase>& cases,
                        const std::string& extra = "") {
  std::string src = ThreadSource(cases, extra);
  SimFixture f;
  RunSequenceDesign(src, f);
  for (size_t i = 0; i < cases.size(); ++i) {
    std::string label = "c" + std::to_string(i + 1) + ":";
    EXPECT_EQ(CoverCount(f, src, label), cases[i].matches)
        << label << " " << cases[i].body;
  }
}

constexpr const char* kShortFirst =
    "(((te1, x = 1) ##1 1) or ((te1, x = 2) ##2 1))";
constexpr const char* kLongFirst =
    "(((te1, x = 2) ##2 1) or ((te1, x = 1) ##1 1))";

std::string Then(const char* head, const char* tail) {
  return std::string(head) + " ##1 " + tail;
}

TEST(OrThreadValues, DISABLED_OperandsEndingAtDifferentTicksKeepTheirValues) {
  ExpectThreadCounts({
      {Then(kShortFirst, "(x == 1)"), 2},
      {Then(kLongFirst, "(x == 1)"), 2},
      {Then(kShortFirst, "(x == 2)"), 2},
      {Then(kLongFirst, "(x == 2)"), 2},
  });
}

TEST(OrThreadValues, DISABLED_OperandsEndingAtTheSameTickKeepTheirValues) {
  ExpectThreadCounts({
      {"(((te1, x = 1) ##1 1) or ((te1, x = 2) ##1 1)) ##1 (x == 1)", 2},
      {"(((te1, x = 1) ##1 1) or ((te1, x = 2) ##1 1)) ##1 (x == 2)", 2},
      {"(((te1, x = 2) ##1 1) or ((te1, x = 1) ##1 1)) ##1 (x == 1)", 2},
      {"(((te1, x = 2) ##1 1) or ((te1, x = 1) ##1 1)) ##1 (x == 2)", 2},
      {"((te1, x = 1) or (te1, x = 2)) ##1 (x == 1)", 2},
      {"((te1, x = 1) or (te1, x = 2)) ##1 (x == 2)", 2},
  });
}

TEST(OrThreadValues,
     DISABLED_AnOperandThatAssignsNothingKeepsTheValueThatFlowedIn) {
  ExpectThreadCounts({
      {"(te1, x = 0) ##0 (((1, x = 1) ##1 1) or (1 ##2 1)) ##1 (x == 0)", 2},
      {"(te1, x = 0) ##0 ((1 ##2 1) or ((1, x = 1) ##1 1)) ##1 (x == 0)", 2},
      {"(te1, x = 0) ##0 (((1, x = 1) ##1 1) or (1 ##2 1)) ##1 (x == 1)", 2},
      {"(te1, x = 0) ##0 (((1, x = 1) ##1 1) or ((1, x = 2) ##2 1)) ##1"
       " (x == 2)",
       2},
      {"(te1, x = 0) ##0 (((1, x = 1) ##1 1) or ((1, x = 2) ##2 1)) ##1"
       " (x == 0)",
       0},
  });
}

TEST(OrThreadValues, DISABLED_AGroupsMatchItemReadsEachThreadsValue) {
  ExpectThreadCounts({
      {std::string("(") + kShortFirst + ", y = x) ##1 (y == 1)", 2},
      {std::string("(") + kShortFirst + ", y = x) ##1 (y == 2)", 2},
      {std::string("(") + kLongFirst + ", y = x) ##1 (y == 1)", 2},
  });
}

TEST(OrThreadValues, DISABLED_ANestedOrKeepsThreeValues) {
  const std::string kNested =
      std::string("(") + kShortFirst + " or ((te1, x = 3) ##3 1))";
  ExpectThreadCounts({
      {kNested + " ##1 (x == 1)", 2},
      {kNested + " ##1 (x == 2)", 2},
      {kNested + " ##1 (x == 3)", 2},
  });
}

TEST(OrThreadValues, DISABLED_InstanceOperandsKeepTheirValues) {
  const std::string kSub =
      "  sequence sub(lv, int v, int n); (te1, lv = v) ##n 1; endsequence\n";
  ExpectThreadCounts(
      {
          {"(sub(x, 1, 1) or sub(x, 2, 2)) ##1 (x == 1)", 2},
          {"(sub(x, 2, 2) or sub(x, 1, 1)) ##1 (x == 1)", 2},
          {"(sub(x, 2, 2) or sub(x, 1, 1)) ##1 (x == 2)", 2},
      },
      kSub);
}

TEST(OrThreadValues, DISABLED_AnAntecedentOrKeepsEachThreadsValue) {
  std::string src =
      SequenceCoverSource(std::string("  int f1 = 0, f2 = 0, f3 = 0;\n"
                                      "  property p1; int x; @(posedge clk) ") +
                              kLongFirst +
                              " |=> (x == 1); endproperty\n"
                              "  property p2; int x; @(posedge clk) " +
                              kShortFirst +
                              " |-> ##1 (x == 2); endproperty\n"
                              "  property p3; int x; @(posedge clk) " +
                              kLongFirst +
                              " |=> (x == 1 || x == 2); endproperty\n"
                              "  assert property (p1) else f1++;\n"
                              "  assert property (p2) else f2++;\n"
                              "  assert property (p3) else f3++;\n"
                              "  c1: cover property (p1);\n"
                              "  c2: cover property (p3);\n",
                          ThreadDrive());
  SimFixture f;
  RunSequenceDesign(src, f);
  EXPECT_EQ(VarValue(f, "f1"), 2u);
  EXPECT_EQ(VarValue(f, "f2"), 2u);
  EXPECT_EQ(VarValue(f, "f3"), 0u);
  EXPECT_EQ(CoverCount(f, src, "c1:"), 0u);
  EXPECT_EQ(CoverCount(f, src, "c2:"), 2u);
}

TEST(OrThreadValues, DISABLED_EveryDesignElementKeepsEachThreadsValue) {
  std::string src = DesignElementCoverSource(
      "cover sequence (so);\n"
      "  sequence so; int x;\n"
      "    @(posedge clk) (((te1, x = 1) ##1 1) or ((te1, x = 2) ##2 1))"
      " ##1 (x == 1);\n"
      "  endsequence\n",
      ThreadDrive());
  SimFixture f;
  RunSequenceDesign(src, f);
  for (const char* label : {"i1:", "p1:", "k1:", "g1:"}) {
    EXPECT_EQ(CoverCount(f, src, label), 2u) << label;
  }
}

TEST(OrThreadValues, DISABLED_APackageSequenceKeepsEachThreadsValue) {
  std::string src = SequenceCoverSource(
      "  c1: cover sequence (@(posedge clk) pk::so(te1));\n", ThreadDrive(),
      "package pk;\n"
      "  sequence so(a); int x;\n"
      "    (((a, x = 1) ##1 1) or ((a, x = 2) ##2 1)) ##1 (x == 1);\n"
      "  endsequence\n"
      "endpackage\n");
  SimFixture f;
  RunSequenceDesign(src, f);
  EXPECT_EQ(CoverCount(f, src, "c1:"), 2u);
}

TEST(MergedFlowValues, ALocalFromOneOperandFlowsOutWithItsValue) {
  for (const char* op : {"and", "intersect"}) {
    std::string o = op;
    ExpectThreadCounts({
        {"((te1, x = 1) " + o + " (te1, y = 2)) ##1 (x == 1 && y == 2)", 2},
        {"(te1, x = 0) ##0 (((1, x = 4) ##1 1) " + o +
             " (1 ##1 1)) ##1 (x == 4)",
         2},
        {"(te1, x = 0) ##0 ((1 ##1 1) " + o +
             " ((1, x = 4) ##1 1)) ##1 (x == 0)",
         0},
        {"(te1, x = 5) ##0 ((1 ##1 1) " + o + " (1 ##1 1)) ##1 (x == 5)", 2},
    });
  }
}

TEST(MergedFlowValues, TheShorterOperandOfAndKeepsItsValue) {
  ExpectThreadCounts({
      {"((te1, x = 3) and (te1 ##2 1)) ##1 (x == 3)", 2},
      {"((te1 ##2 1) and (te1, x = 3)) ##1 (x == 3)", 2},
      {"(te1, x = 0) ##0 ((1, x = 3) and (1 ##2 1)) ##1 (x == 3)", 2},
      {"(te1, x = 0) ##0 ((1 ##2 1) and (1, x = 3)) ##1 (x == 0)", 0},
  });
}

TEST(MergedFlowValues, AnInnerLocalFlowsOutOfWithin) {
  ExpectThreadCounts({
      {"((te1, x = 4) within (te1 ##2 1)) ##1 (x == 4)", 2},
      {"(te1, x = 0) ##0 ((te1, x = 4) within (1 ##2 1)) ##1 (x == 4)", 2},
  });
}

}  // namespace
