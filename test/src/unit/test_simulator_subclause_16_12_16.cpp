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

// §16.12.16: during the linear search the first item whose expression matches
// the case expression is the property statement that is evaluated, and the
// search terminates there. A later matching item with a different verdict is
// therefore never reached.
TEST(PropertyCase, FirstMatchingItemSelectedAndSearchTerminates) {
  std::vector<PropertyCaseBranch> branches = {
      {/*selected=*/false, PropertyResult::kFail},
      {/*selected=*/true, PropertyResult::kPass},
      {/*selected=*/true, PropertyResult::kFail},
  };
  EXPECT_EQ(
      EvalPropertyCase(branches, /*has_default=*/false, PropertyResult::kFail),
      PropertyResult::kPass);
}

// §16.12.16: the verdict the case property returns is exactly that of the
// selected item's property_expr, including a failing one.
TEST(PropertyCase, SelectedItemVerdictPropagates) {
  std::vector<PropertyCaseBranch> branches = {
      {/*selected=*/false, PropertyResult::kPass},
      {/*selected=*/true, PropertyResult::kFail},
  };
  EXPECT_EQ(
      EvalPropertyCase(branches, /*has_default=*/false, PropertyResult::kPass),
      PropertyResult::kFail);

  std::vector<PropertyCaseBranch> vacuous = {
      {/*selected=*/true, PropertyResult::kVacuousPass},
  };
  EXPECT_EQ(
      EvalPropertyCase(vacuous, /*has_default=*/false, PropertyResult::kFail),
      PropertyResult::kVacuousPass);

  // An as-yet unresolved verdict from the selected item is carried through
  // unchanged rather than normalized — the case result tracks the chosen item.
  std::vector<PropertyCaseBranch> pending = {
      {/*selected=*/true, PropertyResult::kPending},
  };
  EXPECT_EQ(
      EvalPropertyCase(pending, /*has_default=*/false, PropertyResult::kPass),
      PropertyResult::kPending);
}

// §16.12.16: if there is a default item it is ignored during the linear search.
// A matching ordinary item is taken even though a default is present, so the
// default verdict does not influence the result.
TEST(PropertyCase, DefaultIgnoredDuringLinearSearch) {
  std::vector<PropertyCaseBranch> branches = {
      {/*selected=*/false, PropertyResult::kFail},
      {/*selected=*/true, PropertyResult::kPass},
  };
  EXPECT_EQ(EvalPropertyCase(branches, /*has_default=*/true,
                             /*default_result=*/PropertyResult::kFail),
            PropertyResult::kPass);
}

// §16.12.16: if all comparisons fail and a default item is given, the default
// item's property statement is executed and provides the verdict.
TEST(PropertyCase, DefaultExecutedWhenAllComparisonsFail) {
  std::vector<PropertyCaseBranch> branches = {
      {/*selected=*/false, PropertyResult::kPass},
      {/*selected=*/false, PropertyResult::kPass},
  };
  EXPECT_EQ(EvalPropertyCase(branches, /*has_default=*/true,
                             /*default_result=*/PropertyResult::kFail),
            PropertyResult::kFail);
  EXPECT_EQ(EvalPropertyCase(branches, /*has_default=*/true,
                             /*default_result=*/PropertyResult::kPass),
            PropertyResult::kPass);
}

// §16.12.16: if the default item is not given and all comparisons fail, none of
// the item property statements is evaluated and the case property succeeds
// vacuously from that start point, returning true.
TEST(PropertyCase, NoDefaultAllComparisonsFailSucceedsVacuously) {
  std::vector<PropertyCaseBranch> branches = {
      {/*selected=*/false, PropertyResult::kFail},
      {/*selected=*/false, PropertyResult::kFail},
  };
  EXPECT_EQ(
      EvalPropertyCase(branches, /*has_default=*/false, PropertyResult::kFail),
      PropertyResult::kVacuousPass);
}

// §16.12.16: the empty-ordinary-item boundary — a case property whose only item
// is the default. With no ordinary items the linear search finds no match, so
// the default item's property statement supplies the verdict.
TEST(PropertyCase, EmptyItemListWithDefaultExecutesDefault) {
  std::vector<PropertyCaseBranch> branches;
  EXPECT_EQ(EvalPropertyCase(branches, /*has_default=*/true,
                             /*default_result=*/PropertyResult::kFail),
            PropertyResult::kFail);
  EXPECT_EQ(EvalPropertyCase(branches, /*has_default=*/true,
                             /*default_result=*/PropertyResult::kPass),
            PropertyResult::kPass);
}

// The design of test/src/e2e/case_property.sv around one assertion: clk
// rises at 5, 15, ..., 75 so that tick n is at 10n - 5; delay is 0 at ticks
// 1 and 2, 1 at 3 and 4, 2 at 5 and 6 and 3 at 7 and 8; a is high
// throughout, b at 2, 3, 4 and 8, and sel_x is 2'bxx.
std::string CaseSource(const std::string& items) {
  return "module t;\n"
         "  logic clk = 0;\n"
         "  int tick = 1;\n"
         "  logic [1:0] delay;\n"
         "  logic [1:0] sel_x = 2'bxx;\n"
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

// The pass and fail counts of the assertion over `spec`, its property the
// case written in the design's terms.
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

// §16.12.16: the clause's decoding of a variable delay, the item taking
// delay's value at the attempt's tick and its sequence running from it:
// `a && b` at 1 and 2, `a ##1 b` from 3 and 4, `a ##2 b` from 5 and 6 and
// the default at 7 and 8, so 2, 3 and 6 pass and the other five fail.
TEST(PropertyCase, TheItemSelectedAtTheTickRunsItsSequenceFromIt) {
  auto counts = CountsOf(
      "case (delay) 2'd0: a && b; 2'd1: a ##1 b; 2'd2: a ##2 b; "
      "default: 0; endcase");
  EXPECT_EQ(counts.first, 3u);
  EXPECT_EQ(counts.second, 5u);
}

// §16.12.16: the linear search ends at the first item matching, so the
// item repeating 2'd1 never inverts the verdicts at 3 and 4, and the
// default written first is ignored in the search: b holds at 2, 3 and 4
// and !b at 5, 6 and 7, six passes.
TEST(PropertyCase, TheSearchEndsAtTheFirstMatchAndPassesTheDefault) {
  auto counts = CountsOf(
      "case (delay) default: 0; 2'd0, 2'd1: b; 2'd1: !b; 2'd2, 2'd3: !b; "
      "endcase");
  EXPECT_EQ(counts.first, 6u);
  EXPECT_EQ(counts.second, 2u);
}

// §16.12.16: with no item for delay 1 or 2 and no default, the attempts
// from 3 to 6 evaluate no item and succeed vacuously, beside b at 2 and !b
// at 7.
TEST(PropertyCase, NoMatchAndNoDefaultHoldsVacuously) {
  auto counts = CountsOf("case (delay) 2'd0: b; 2'd3: !b; endcase");
  EXPECT_EQ(counts.first, 6u);
  EXPECT_EQ(counts.second, 2u);
}

// §16.12.16: an item's property may be a case of its own, the default's
// colon optional: b at 1 and 2, !b at 3 and 4 and a from 5.
TEST(PropertyCase, AnItemsPropertyMayBeACase) {
  auto counts = CountsOf(
      "case (delay[1]) 1'b0: case (delay[0]) 1'b0: b; default !b; endcase; "
      "default: a; endcase");
  EXPECT_EQ(counts.first, 5u);
  EXPECT_EQ(counts.second, 3u);
}

// §16.12.16 and §12.5: the case expression is compared with the items by
// case equality, so sel_x, 2'bxx, matches the item 2'bxx and not 2'b00.
TEST(PropertyCase, TheItemsAreComparedByCaseEquality) {
  auto counts =
      CountsOf("case (sel_x) 2'b00: 0; 2'bxx: 1; default: 0; endcase");
  EXPECT_EQ(counts.first, 8u);
  EXPECT_EQ(counts.second, 0u);
}

}  // namespace
