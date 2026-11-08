#include <gtest/gtest.h>

#include <cstdint>
#include <string>
#include <utility>
#include <vector>

#include "fixture_simulator.h"
#include "simulator/sva_engine_sampling.h"
#include "simulator/sva_engine_sequences.h"
#include "simulator/variable.h"

using namespace delta;

namespace {

TEST(SequenceProperty, BareSequenceIsWeakUnderAssertAndAssume) {
  EXPECT_EQ(DefaultSequencePropertyStrength(AssertionKind::kAssert),
            SequencePropertyStrength::kWeak);
  EXPECT_EQ(DefaultSequencePropertyStrength(AssertionKind::kAssume),
            SequencePropertyStrength::kWeak);
}

TEST(SequenceProperty, BareSequenceIsStrongOtherwise) {
  EXPECT_EQ(DefaultSequencePropertyStrength(AssertionKind::kCover),
            SequencePropertyStrength::kStrong);
  EXPECT_EQ(DefaultSequencePropertyStrength(AssertionKind::kRestrict),
            SequencePropertyStrength::kStrong);
}

TEST(SequenceProperty, StrongHoldsExactlyWhenNonemptyMatchExists) {
  EXPECT_EQ(EvalStrongSequenceProperty(true), PropertyResult::kPass);
  EXPECT_EQ(EvalStrongSequenceProperty(false), PropertyResult::kFail);
}

TEST(SequenceProperty, WeakFailsOnlyWhenAPrefixWitnessesInability) {
  EXPECT_EQ(EvalWeakSequenceProperty(false), PropertyResult::kPass);
  EXPECT_EQ(EvalWeakSequenceProperty(true), PropertyResult::kFail);
}

const std::vector<std::vector<uint32_t>>& OperandMatchSets() {
  static const std::vector<std::vector<uint32_t>> kSets = {
      {}, {7}, {5, 3, 4, 2}, {4, 4, 6}, {3, 3, 3},
  };
  return kSets;
}

TEST(SequenceProperty, StrongEqualsStrongOfFirstMatch) {
  for (const auto& match_set : OperandMatchSets()) {
    bool seq_has_match = !match_set.empty();
    bool first_match_has_match = EvalFirstMatch(match_set).matched;
    EXPECT_EQ(EvalStrongSequenceProperty(seq_has_match),
              EvalStrongSequenceProperty(first_match_has_match));
  }
}

TEST(SequenceProperty, WeakEqualsWeakOfFirstMatch) {
  for (const auto& match_set : OperandMatchSets()) {
    bool seq_prefix_inability = match_set.empty();
    bool first_match_prefix_inability = !EvalFirstMatch(match_set).matched;
    EXPECT_EQ(EvalWeakSequenceProperty(seq_prefix_inability),
              EvalWeakSequenceProperty(first_match_prefix_inability));
  }
}

std::string SequencePropertySource(const std::string& items) {
  return "module t;\n"
         "  logic clk = 0;\n"
         "  int tick = 1;\n"
         "  logic b, c, go;\n"
         "  int passes = 0;\n"
         "  int fails = 0;\n"
         "  always #5 clk = ~clk;\n"
         "  always #10 tick = tick + 1;\n"
         "  assign b = tick inside {2, 3, 4};\n"
         "  assign c = tick inside {3};\n"
         "  assign go = tick inside {4};\n" +
         items +
         "  initial #40 $finish;\n"
         "endmodule\n";
}

TEST(SequenceProperty, BareSequenceInAssertIsWeak) {
  SimFixture f;
  auto* passes = RunAndFindVar(
      SequencePropertySource("  a: assert property (@(posedge clk) b ##1 c) "
                             "passes++; else fails++;\n"),
      f, "passes");
  ASSERT_NE(passes, nullptr);
  EXPECT_EQ(passes->value.ToUint64(), 1u);
  EXPECT_EQ(f.ctx.FindVariable("fails")->value.ToUint64(), 2u);
}

TEST(SequenceProperty, StrongSequenceFailsWhenUnfinishedAtTheEnd) {
  SimFixture f;
  auto* passes = RunAndFindVar(
      SequencePropertySource(
          "  a: assert property (@(posedge clk) strong(b ##1 c)) passes++; "
          "else fails++;\n"),
      f, "passes");
  ASSERT_NE(passes, nullptr);
  EXPECT_EQ(passes->value.ToUint64(), 1u);
  EXPECT_EQ(f.ctx.FindVariable("fails")->value.ToUint64(), 2u);
  f.ctx.RunFinalBlocks();
  EXPECT_EQ(f.ctx.FindVariable("fails")->value.ToUint64(), 3u);
}

TEST(SequenceProperty, WeakSequenceWrittenOutIsTheBareForm) {
  SimFixture f;
  auto* passes = RunAndFindVar(
      SequencePropertySource(
          "  a: assert property (@(posedge clk) weak(b ##1 c)) passes++; "
          "else fails++;\n"),
      f, "passes");
  ASSERT_NE(passes, nullptr);
  EXPECT_EQ(passes->value.ToUint64(), 1u);
  EXPECT_EQ(f.ctx.FindVariable("fails")->value.ToUint64(), 2u);
}

TEST(SequenceProperty, BareSequenceInCoverIsStrong) {
  SimFixture f;
  auto* passes = RunAndFindVar(
      SequencePropertySource(
          "  cv: cover property (@(posedge clk) b ##1 c) passes++;\n"),
      f, "passes");
  ASSERT_NE(passes, nullptr);
  EXPECT_EQ(passes->value.ToUint64(), 1u);
}

uint64_t NamedSequenceCoverPasses(const std::string& directive) {
  SimFixture f;
  auto* passes = RunAndFindVar(
      SequencePropertySource("  sequence s; @(posedge clk) b ##1 c; "
                             "endsequence\n"
                             "  cv: " +
                             directive + " (s) passes++;\n"),
      f, "passes");
  if (passes == nullptr) return 0;
  f.ctx.RunFinalBlocks();
  return passes->value.ToUint64();
}

TEST(SequenceProperty, NamedSequenceInCoverPropertyIsStrong) {
  EXPECT_EQ(NamedSequenceCoverPasses("cover property"), 1u);
}

TEST(SequenceProperty, NamedSequenceInCoverSequenceIsStrong) {
  EXPECT_EQ(NamedSequenceCoverPasses("cover sequence"), 1u);
}

std::pair<uint64_t, uint64_t> CountsAtTheEnd(const std::string& items) {
  SimFixture f;
  auto* passes = RunAndFindVar(SequencePropertySource(items), f, "passes");
  if (passes == nullptr) return {~0ull, ~0ull};
  f.ctx.RunFinalBlocks();
  return {passes->value.ToUint64(),
          f.ctx.FindVariable("fails")->value.ToUint64()};
}

TEST(SequenceProperty, PlainSequenceBeneathAnOperatorInCoverIsStrong) {
  auto counts = CountsAtTheEnd(
      "  cv: cover property (@(posedge clk) (b ##1 c) or (b ##2 c)) "
      "passes++;\n");
  EXPECT_EQ(counts.first, 1u);
}

TEST(SequenceProperty, PlainSequenceBeneathAnOperatorInAssertIsWeak) {
  auto counts = CountsAtTheEnd(
      "  a: assert property (@(posedge clk) (b ##1 c) or (b ##2 c)) "
      "passes++; else fails++;\n");
  EXPECT_EQ(counts.first, 3u);
  EXPECT_EQ(counts.second, 1u);
}

TEST(SequenceProperty, PlainSequenceOfAPropertyBodyIsStrongInACover) {
  auto counts = CountsAtTheEnd(
      "  property p3; b ##1 c; endproperty\n"
      "  cv: cover property (@(posedge clk) go #-# p3) passes++;\n");
  EXPECT_EQ(counts.first, 0u);
}

TEST(SequenceProperty, WeakSequenceBeneathAnOperatorInCoverIsWeak) {
  auto counts = CountsAtTheEnd(
      "  cv: cover property (@(posedge clk) weak(b ##1 c) or weak(b ##2 c)) "
      "passes++;\n");
  EXPECT_EQ(counts.first, 3u);
}

TEST(SequenceProperty, PlainSequenceInExpectIsStrong) {
  auto counts = CountsAtTheEnd(
      "  initial begin #30; expect (@(posedge clk) b ##1 c) passes++; "
      "else fails++; end\n");
  EXPECT_EQ(counts.first, 0u);
  EXPECT_EQ(counts.second, 1u);
}

TEST(SequenceProperty, PlainSequenceBeneathAnOperatorInExpectIsStrong) {
  auto counts = CountsAtTheEnd(
      "  initial begin #30; expect (@(posedge clk) (b ##1 c) or (b ##2 c)) "
      "passes++; else fails++; end\n");
  EXPECT_EQ(counts.first, 0u);
  EXPECT_EQ(counts.second, 1u);
}

TEST(SequenceProperty, WeakSequenceInExpectIsWeak) {
  auto counts = CountsAtTheEnd(
      "  initial begin #30; expect (@(posedge clk) weak(b ##1 c)) passes++; "
      "else fails++; end\n");
  EXPECT_EQ(counts.first, 0u);
  EXPECT_EQ(counts.second, 0u);
}

}  // namespace
