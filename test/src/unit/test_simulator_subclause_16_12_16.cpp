#include <gtest/gtest.h>

#include <cstdint>
#include <string>
#include <utility>
#include <vector>

#include "fixture_simulator.h"
#include "simulator/sva_engine_properties.h"
#include "simulator/sva_engine_sequences.h"
#include "simulator/variable.h"

using namespace delta;

namespace {

TEST(PropertyCase, FirstMatchingItemSelectedAndSearchTerminates) {
  std::vector<PropertyCaseBranch> branches = {
      {false, PropertyResult::kFail},
      {true, PropertyResult::kPass},
      {true, PropertyResult::kFail},
  };
  EXPECT_EQ(EvalPropertyCase(branches, false, PropertyResult::kFail),
            PropertyResult::kPass);
}

TEST(PropertyCase, SelectedItemVerdictPropagates) {
  std::vector<PropertyCaseBranch> branches = {
      {false, PropertyResult::kPass},
      {true, PropertyResult::kFail},
  };
  EXPECT_EQ(EvalPropertyCase(branches, false, PropertyResult::kPass),
            PropertyResult::kFail);

  std::vector<PropertyCaseBranch> vacuous = {
      {true, PropertyResult::kVacuousPass},
  };
  EXPECT_EQ(EvalPropertyCase(vacuous, false, PropertyResult::kFail),
            PropertyResult::kVacuousPass);

  std::vector<PropertyCaseBranch> pending = {
      {true, PropertyResult::kPending},
  };
  EXPECT_EQ(EvalPropertyCase(pending, false, PropertyResult::kPass),
            PropertyResult::kPending);
}

TEST(PropertyCase, DefaultIgnoredDuringLinearSearch) {
  std::vector<PropertyCaseBranch> branches = {
      {false, PropertyResult::kFail},
      {true, PropertyResult::kPass},
  };
  EXPECT_EQ(EvalPropertyCase(branches, true, PropertyResult::kFail),
            PropertyResult::kPass);
}

TEST(PropertyCase, DefaultExecutedWhenAllComparisonsFail) {
  std::vector<PropertyCaseBranch> branches = {
      {false, PropertyResult::kPass},
      {false, PropertyResult::kPass},
  };
  EXPECT_EQ(EvalPropertyCase(branches, true, PropertyResult::kFail),
            PropertyResult::kFail);
  EXPECT_EQ(EvalPropertyCase(branches, true, PropertyResult::kPass),
            PropertyResult::kPass);
}

TEST(PropertyCase, NoDefaultAllComparisonsFailSucceedsVacuously) {
  std::vector<PropertyCaseBranch> branches = {
      {false, PropertyResult::kFail},
      {false, PropertyResult::kFail},
  };
  EXPECT_EQ(EvalPropertyCase(branches, false, PropertyResult::kFail),
            PropertyResult::kVacuousPass);
}

TEST(PropertyCase, EmptyItemListWithDefaultExecutesDefault) {
  std::vector<PropertyCaseBranch> branches;
  EXPECT_EQ(EvalPropertyCase(branches, true, PropertyResult::kFail),
            PropertyResult::kFail);
  EXPECT_EQ(EvalPropertyCase(branches, true, PropertyResult::kPass),
            PropertyResult::kPass);
}

std::string CaseSource(const std::string& items) {
  return "module t;\n"
         "  logic clk = 0;\n"
         "  int tick = 1;\n"
         "  logic [1:0] delay;\n"
         "  logic [1:0] sel_x = 2'bxx;\n"
         "  logic signed [3:0] minus_one = -1;\n"
         "  logic [3:0] eight = 8;\n"
         "  logic a = 1;\n"
         "  logic b;\n"
         "  int passes = 0;\n"
         "  int fails = 0;\n"
         "  always #5 clk = ~clk;\n"
         "  always #10 tick = tick + 1;\n"
         "  assign delay = (tick - 1) / 2;\n"
         "  assign b = tick inside {2, 3, 4, 8};\n" +
         items +
         "  initial #80 $finish;\n"
         "endmodule\n";
}

std::pair<uint64_t, uint64_t> CountsOf(const std::string& spec) {
  SimFixture f;
  auto* passes =
      RunAndFindVar(CaseSource("  p: assert property (@(posedge clk) " + spec +
                               ") passes++; else fails++;\n"),
                    f, "passes");
  if (passes == nullptr) return {~0ull, ~0ull};
  return {passes->value.ToUint64(),
          f.ctx.FindVariable("fails")->value.ToUint64()};
}

TEST(PropertyCase, TheItemSelectedAtTheTickRunsItsSequenceFromIt) {
  auto counts = CountsOf(
      "case (delay) 2'd0: a && b; 2'd1: a ##1 b; 2'd2: a ##2 b; "
      "default: 0; endcase");
  EXPECT_EQ(counts.first, 3u);
  EXPECT_EQ(counts.second, 5u);
}

TEST(PropertyCase, TheSearchEndsAtTheFirstMatchAndPassesTheDefault) {
  auto counts = CountsOf(
      "case (delay) default: 0; 2'd0, 2'd1: b; 2'd1: !b; 2'd2, 2'd3: !b; "
      "endcase");
  EXPECT_EQ(counts.first, 6u);
  EXPECT_EQ(counts.second, 2u);
}

TEST(PropertyCase, NoMatchAndNoDefaultHoldsVacuously) {
  auto counts = CountsOf("case (delay) 2'd0: b; 2'd3: !b; endcase");
  EXPECT_EQ(counts.first, 6u);
  EXPECT_EQ(counts.second, 2u);
}

TEST(PropertyCase, AnItemsPropertyMayBeACase) {
  auto counts = CountsOf(
      "case (delay[1]) 1'b0: case (delay[0]) 1'b0: b; default !b; endcase; "
      "default: a; endcase");
  EXPECT_EQ(counts.first, 5u);
  EXPECT_EQ(counts.second, 3u);
}

TEST(PropertyCase, TheItemsAreComparedByCaseEquality) {
  auto counts =
      CountsOf("case (sel_x) 2'b00: 0; 2'bxx: 1; default: 0; endcase");
  EXPECT_EQ(counts.first, 8u);
  EXPECT_EQ(counts.second, 0u);
}

TEST(PropertyCase, TheExpressionsAreEvaluatedAtTheLongestLength) {
  auto counts = CountsOf("case (eight + eight) 8'd16: 1; default: 0; endcase");
  EXPECT_EQ(counts.first, 8u);
  EXPECT_EQ(counts.second, 0u);
}

TEST(PropertyCase, AnUnsignedItemMakesEveryComparisonUnsigned) {
  auto counts = CountsOf(
      "case (minus_one) 8'sb1111_1111: 0; 8'd5: 0; default: 1; endcase");
  EXPECT_EQ(counts.first, 8u);
  EXPECT_EQ(counts.second, 0u);
}

TEST(PropertyCase, WhereEveryExpressionIsSignedTheExtensionIsBySign) {
  auto counts =
      CountsOf("case (minus_one) 8'sb1111_1111: 1; default: 0; endcase");
  EXPECT_EQ(counts.first, 8u);
  EXPECT_EQ(counts.second, 0u);
}

}  // namespace
