#include <gtest/gtest.h>

#include <cstdint>
#include <string>
#include <string_view>

#include "fixture_simulator.h"
#include "helpers_reported_error.h"
#include "helpers_sequence_ticks.h"
#include "simulator/cover_results.h"
#include "simulator/cover_statement.h"

using namespace delta;

namespace {

constexpr const char* kRangeAnd = "(te1 ##[1:5] te2) and (te3 ##2 te4 ##2 te5)";
constexpr const char* kFixedAnd = "(te1 ##2 te2) and (te3 ##2 te4 ##2 te5)";
constexpr uint64_t kNoRecord = ~uint64_t{0};

std::string RangeDrive() {
  return DriveTicks(
      {{1, 2, 8}, {9, 10, 11, 12, 13}, {2, 3, 8}, {4, 10}, {6, 12}});
}

std::string FixedDrive() {
  return DriveTicks({{1, 2, 8}, {10, 12, 13}, {2, 3, 8}, {4, 10}, {6, 12}});
}

std::string AndSource(const std::string& items, const std::string& drive,
                      const std::string& outside = "") {
  return outside +
         "module t;\n"
         "  logic clk = 0;\n"
         "  logic te1 = 0, te2 = 0, te3 = 0, te4 = 0, te5 = 0;\n"
         "  int fails = 0;\n"
         "  int at = 0;\n"
         "  always #5 clk = ~clk;\n" +
         items + "  initial begin\n" + drive +
         "    #10 $finish;\n"
         "  end\n"
         "endmodule\n";
}

void RunDesign(const std::string& src, SimFixture& f) {
  auto* design = ElaborateSrc(src, f);
  ASSERT_NE(design, nullptr);
  LowerAndRun(design, f);
}

uint64_t CoverCount(SimFixture& f, const std::string& src,
                    std::string_view label) {
  uint32_t line = LineHolding(src, label);
  for (const auto& record : f.ctx.ConcurrentCovers().Results()) {
    if (record.line != line) continue;
    return record.category == CoverStatementCategory::kSequence
               ? record.matched
               : record.succeeded;
  }
  return kNoRecord;
}

uint64_t VarValue(SimFixture& f, std::string_view name) {
  auto* var = f.ctx.FindVariable(name);
  return var == nullptr ? kNoRecord : var->value.ToUint64();
}

TEST(SequenceAndMatches, DISABLED_EachPairOfOperandMatchesIsAMatch) {
  std::string items = "  sequence s_and; ";
  items += kRangeAnd;
  items += "; endsequence\n  c1: cover sequence (@(posedge clk) ";
  items += kRangeAnd;
  items += ");\n  c2: cover sequence (@(posedge clk) s_and);\n";
  std::string src = AndSource(items, RangeDrive());
  SimFixture f;
  RunDesign(src, f);
  EXPECT_EQ(CoverCount(f, src, "c1:"), 5u);
  EXPECT_EQ(CoverCount(f, src, "c2:"), 5u);
}

TEST(SequenceAndMatches, ARangeOperandAloneCountsEveryMatch) {
  std::string src = AndSource(
      "  c1: cover sequence (@(posedge clk) te1 ##[1:5] te2);\n", RangeDrive());
  SimFixture f;
  RunDesign(src, f);
  EXPECT_EQ(CoverCount(f, src, "c1:"), 5u);
}

TEST(SequenceAndMatches, DISABLED_SwappedOperandsPairEveryMatch) {
  std::string src = AndSource(
      "  c1: cover sequence (@(posedge clk)"
      " (te3 ##2 te4 ##2 te5) and (te1 ##[1:5] te2));\n",
      RangeDrive());
  SimFixture f;
  RunDesign(src, f);
  EXPECT_EQ(CoverCount(f, src, "c1:"), 5u);
}

TEST(SequenceAndMatches, DISABLED_ABooleanOperandPairsWithEveryRangeMatch) {
  std::string src = AndSource(
      "  c1: cover sequence (@(posedge clk) (te1 ##[1:5] te2) and te1)"
      " at = $time;\n",
      RangeDrive());
  SimFixture f;
  RunDesign(src, f);
  EXPECT_EQ(CoverCount(f, src, "c1:"), 5u);
  EXPECT_EQ(VarValue(f, "at"), 125u);
}

TEST(SequenceAndMatches, DISABLED_TwoRangeOperandsPairEveryMatch) {
  std::string src = AndSource(
      "  c1: cover sequence (@(posedge clk)"
      " (te1 ##[1:2] te2) and (te3 ##[1:2] te2));\n",
      RangeDrive());
  SimFixture f;
  RunDesign(src, f);
  EXPECT_EQ(CoverCount(f, src, "c1:"), 4u);
}

TEST(SequenceAndMatches, DISABLED_EachMatchContinuesTheChainAfterIt) {
  std::string items = "  sequence s_and; ";
  items += kRangeAnd;
  items += "; endsequence\n  c1: cover sequence (@(posedge clk) (";
  items += kRangeAnd;
  items += ") ##1 te2);\n  c2: cover sequence (@(posedge clk) te3 ##0 (";
  items += kRangeAnd;
  items +=
      ") ##1 te2);\n"
      "  c3: cover sequence (@(posedge clk) te3 ##0 s_and ##1 te2);\n";
  std::string src = AndSource(items, RangeDrive());
  SimFixture f;
  RunDesign(src, f);
  EXPECT_EQ(CoverCount(f, src, "c1:"), 4u);
  EXPECT_EQ(CoverCount(f, src, "c2:"), 4u);
  EXPECT_EQ(CoverCount(f, src, "c3:"), 4u);
}

TEST(SequenceAndMatches, ASingleMatchContinuesTheChainAfterIt) {
  std::string items = "  sequence s_and; ";
  items += kFixedAnd;
  items += "; endsequence\n  c1: cover sequence (@(posedge clk) (";
  items += kFixedAnd;
  items += ") ##1 te2) at = $time;\n";
  items += "  c2: cover sequence (@(posedge clk) te3 ##0 (";
  items += kFixedAnd;
  items +=
      ") ##1 te2);\n"
      "  c3: cover sequence (@(posedge clk) te3 ##0 s_and ##1 te2);\n"
      "  c4: cover sequence (@(posedge clk) te1 ##0 s_and ##1 te1);\n";
  std::string src = AndSource(items, FixedDrive());
  SimFixture f;
  RunDesign(src, f);
  EXPECT_EQ(CoverCount(f, src, "c1:"), 1u);
  EXPECT_EQ(VarValue(f, "at"), 125u);
  EXPECT_EQ(CoverCount(f, src, "c2:"), 1u);
  EXPECT_EQ(CoverCount(f, src, "c3:"), 1u);
  EXPECT_EQ(CoverCount(f, src, "c4:"), 0u);
}

TEST(SequenceAndMatches, AnOperandOpeningWithADelayStartsAtTheAttempt) {
  std::string src = AndSource(
      "  c1: cover sequence (@(posedge clk) te3 and ##1 te4) at = $time;\n",
      RangeDrive());
  SimFixture f;
  RunDesign(src, f);
  EXPECT_EQ(CoverCount(f, src, "c1:"), 1u);
  EXPECT_EQ(VarValue(f, "at"), 35u);
}

std::string OutsideSequences() {
  return "package pk;\n"
         "  sequence s_and(a, b, c, d, e);"
         " (a ##[1:5] b) and (c ##2 d ##2 e); endsequence\n"
         "endpackage\n"
         "sequence u_and(a, b, c, d, e);"
         " (a ##[1:5] b) and (c ##2 d ##2 e); endsequence\n";
}

TEST(SequenceAndMatches, APackageSequenceMatchesOnceAnAttempt) {
  std::string src = AndSource(
      "  c1: cover property (@(posedge clk) pk::s_and(te1, te2, te3, te4,"
      " te5));\n",
      RangeDrive(), OutsideSequences());
  SimFixture f;
  RunDesign(src, f);
  EXPECT_EQ(CoverCount(f, src, "c1:"), 1u);
}

TEST(SequenceAndMatches,
     DISABLED_ACompilationUnitSequenceMatchesOnceAnAttempt) {
  std::string src = AndSource(
      "  c2: cover property (@(posedge clk) u_and(te1, te2, te3, te4,"
      " te5));\n",
      RangeDrive(), OutsideSequences());
  SimFixture f;
  RunDesign(src, f);
  EXPECT_EQ(CoverCount(f, src, "c2:"), 1u);
}

TEST(SequenceAndMatches, DISABLED_ASequenceOutsideAModulePairsEveryMatch) {
  std::string src = AndSource(
      "  c1: cover sequence (@(posedge clk) pk::s_and(te1, te2, te3, te4,"
      " te5));\n"
      "  c2: cover sequence (@(posedge clk) u_and(te1, te2, te3, te4,"
      " te5));\n",
      RangeDrive(), OutsideSequences());
  SimFixture f;
  RunDesign(src, f);
  EXPECT_EQ(CoverCount(f, src, "c1:"), 5u);
  EXPECT_EQ(CoverCount(f, src, "c2:"), 5u);
}

std::string DesignElementsSource(const std::string& directive) {
  std::string body = "(@(posedge clk) ";
  body += kRangeAnd;
  body += ");\n";
  std::string outside =
      "interface ifc(input logic clk, te1, te2, te3, te4, te5);\n"
      "  i1: ";
  outside += directive + body;
  outside +=
      "endinterface\n"
      "program pg(input logic clk, te1, te2, te3, te4, te5);\n"
      "  p1: ";
  outside += directive + body;
  outside +=
      "endprogram\n"
      "checker ck(logic clk, logic te1, logic te2, logic te3, logic te4,"
      " logic te5);\n"
      "  k1: ";
  outside += directive + body;
  outside += "endchecker\n";
  return AndSource(
      "  ifc i(clk, te1, te2, te3, te4, te5);\n"
      "  pg p(clk, te1, te2, te3, te4, te5);\n"
      "  ck k(clk, te1, te2, te3, te4, te5);\n",
      RangeDrive(), outside);
}

TEST(SequenceAndMatches, EveryDesignElementMatchesOnceAnAttempt) {
  std::string src = DesignElementsSource("cover property ");
  SimFixture f;
  RunDesign(src, f);
  EXPECT_EQ(CoverCount(f, src, "i1:"), 1u);
  EXPECT_EQ(CoverCount(f, src, "p1:"), 1u);
  EXPECT_EQ(CoverCount(f, src, "k1:"), 1u);
}

TEST(SequenceAndMatches, DISABLED_EveryDesignElementPairsEveryMatch) {
  std::string src = DesignElementsSource("cover sequence ");
  SimFixture f;
  RunDesign(src, f);
  EXPECT_EQ(CoverCount(f, src, "i1:"), 5u);
  EXPECT_EQ(CoverCount(f, src, "p1:"), 5u);
  EXPECT_EQ(CoverCount(f, src, "k1:"), 5u);
}

std::string InstanceOperands() {
  return "  sequence sa(x, y); x ##[1:5] y; endsequence\n"
         "  sequence sb(x, y, z); x ##2 y ##2 z; endsequence\n"
         "  sequence sf(sequence q); q and (te3 ##2 te4 ##2 te5);"
         " endsequence\n"
         "  sequence sm; int v; (te1 ##[1:5] te2, v = 1) and"
         " (te3 ##2 te4 ##2 te5); endsequence\n";
}

TEST(SequenceAndMatches, AProceduralAssertionOfInstancesMatchesOnce) {
  std::string src = AndSource(InstanceOperands() +
                                  "  always @(posedge clk) begin\n"
                                  "    c1: cover property (sa(te1, te2) and"
                                  " sb(te3, te4, te5));\n"
                                  "  end\n",
                              RangeDrive());
  SimFixture f;
  RunDesign(src, f);
  EXPECT_EQ(CoverCount(f, src, "c1:"), 1u);
}

TEST(SequenceAndMatches, EveryKindOfOperandMatchesOnceAnAttempt) {
  std::string src = AndSource(
      InstanceOperands() +
          "  c1: cover property (@(posedge clk) sa(te1, te2) and"
          " sb(te3, te4, te5));\n"
          "  c2: cover property (@(posedge clk) sf(te1 ##[1:5] te2));\n"
          "  c3: cover property (@(posedge clk) sm);\n",
      RangeDrive());
  SimFixture f;
  RunDesign(src, f);
  EXPECT_EQ(CoverCount(f, src, "c1:"), 1u);
  EXPECT_EQ(CoverCount(f, src, "c2:"), 1u);
  EXPECT_EQ(CoverCount(f, src, "c3:"), 1u);
}

TEST(SequenceAndMatches, DISABLED_EveryKindOfOperandPairsEveryMatch) {
  std::string src = AndSource(
      InstanceOperands() +
          "  c1: cover sequence (@(posedge clk) sa(te1, te2) and"
          " sb(te3, te4, te5));\n"
          "  c2: cover sequence (@(posedge clk) sf(te1 ##[1:5] te2));\n"
          "  c3: cover sequence (@(posedge clk) sm);\n",
      RangeDrive());
  SimFixture f;
  RunDesign(src, f);
  EXPECT_EQ(CoverCount(f, src, "c1:"), 5u);
  EXPECT_EQ(CoverCount(f, src, "c2:"), 5u);
  EXPECT_EQ(CoverCount(f, src, "c3:"), 5u);
}

TEST(SequenceAndImplication, AnAntecedentAttemptFailsOnce) {
  std::string items;
  for (const char* directive : {"assert", "assume"}) {
    for (const char* arrow : {"|->", "|=>"}) {
      items += "  ";
      items += directive;
      items += " property (@(posedge clk) (";
      items += kFixedAnd;
      items += ") ";
      items += arrow;
      items += " 1'b0) else fails++;\n";
    }
  }
  std::string src = AndSource(items, FixedDrive());
  SimFixture f;
  RunDesign(src, f);
  EXPECT_EQ(VarValue(f, "fails"), 4u);
}

TEST(SequenceAndImplication, AConsequentNeedsBothOperands) {
  std::string items;
  for (const char* directive : {"assert", "assume"}) {
    items += "  ";
    items += directive;
    items += " property (@(posedge clk) te1 && te3 |-> ";
    items += kFixedAnd;
    items += ") else fails++;\n  ";
    items += directive;
    items +=
        " property (@(posedge clk) te1 && te3 |=>"
        " (te3 ##1 te4) and (##1 te4 ##2 te5)) else fails++;\n";
  }
  std::string src = AndSource(items, FixedDrive());
  SimFixture f;
  RunDesign(src, f);
  EXPECT_EQ(VarValue(f, "fails"), 4u);
}

TEST(SequenceAndImplication, ACoverOfAnImplicationSucceedsWhereBothMatch) {
  std::string items = "  c1: cover property (@(posedge clk) (";
  items += kFixedAnd;
  items += ") |-> te5);\n  c2: cover property (@(posedge clk) (";
  items += kFixedAnd;
  items += ") |=> te2);\n  c3: cover property (@(posedge clk) te1 && te3 |-> ";
  items += kFixedAnd;
  items +=
      ");\n"
      "  c4: cover property (@(posedge clk) te1 && te3 |=>"
      " (te3 ##1 te4) and (##1 te4 ##2 te5));\n";
  std::string src = AndSource(items, FixedDrive());
  SimFixture f;
  RunDesign(src, f);
  EXPECT_EQ(CoverCount(f, src, "c1:"), 1u);
  EXPECT_EQ(CoverCount(f, src, "c2:"), 1u);
  EXPECT_EQ(CoverCount(f, src, "c3:"), 1u);
  EXPECT_EQ(CoverCount(f, src, "c4:"), 1u);
}

}  // namespace
