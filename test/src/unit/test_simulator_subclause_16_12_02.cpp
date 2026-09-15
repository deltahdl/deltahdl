#include <gtest/gtest.h>

#include <cstdint>
#include <string>
#include <vector>

#include "fixture_simulator.h"
#include "simulator/sva_engine.h"
#include "simulator/variable.h"

using namespace delta;

namespace {

// §16.12.2: when the strong/weak operator is omitted, a bare sequence_expr is
// evaluated weakly inside an assert property or assume property statement.
TEST(SequenceProperty, BareSequenceIsWeakUnderAssertAndAssume) {
  EXPECT_EQ(DefaultSequencePropertyStrength(AssertionKind::kAssert),
            SequencePropertyStrength::kWeak);
  EXPECT_EQ(DefaultSequencePropertyStrength(AssertionKind::kAssume),
            SequencePropertyStrength::kWeak);
}

// §16.12.2: a bare sequence_expr is evaluated strongly inside every other
// assertion statement (the "otherwise" case, e.g. cover property).
TEST(SequenceProperty, BareSequenceIsStrongOtherwise) {
  EXPECT_EQ(DefaultSequencePropertyStrength(AssertionKind::kCover),
            SequencePropertyStrength::kStrong);
  EXPECT_EQ(DefaultSequencePropertyStrength(AssertionKind::kRestrict),
            SequencePropertyStrength::kStrong);
}

// §16.12.2: strong(sequence_expr) evaluates to true if, and only if, there is a
// nonempty match of the sequence_expr. Because a single match suffices, this is
// equivalent to strong(first_match(sequence_expr)).
TEST(SequenceProperty, StrongHoldsExactlyWhenNonemptyMatchExists) {
  EXPECT_EQ(EvalStrongSequenceProperty(/*has_nonempty_match=*/true),
            PropertyResult::kPass);
  EXPECT_EQ(EvalStrongSequenceProperty(/*has_nonempty_match=*/false),
            PropertyResult::kFail);
}

// §16.12.2: weak(sequence_expr) evaluates to true if, and only if, no finite
// prefix witnesses inability to match the sequence_expr. Equivalent to
// weak(first_match(sequence_expr)).
TEST(SequenceProperty, WeakFailsOnlyWhenAPrefixWitnessesInability) {
  EXPECT_EQ(
      EvalWeakSequenceProperty(/*finite_prefix_witnesses_inability=*/false),
      PropertyResult::kPass);
  EXPECT_EQ(
      EvalWeakSequenceProperty(/*finite_prefix_witnesses_inability=*/true),
      PropertyResult::kFail);
}

// Return a spread of operand match sets, each given as the clock ticks on which
// a match of the underlying sequence_expr ends. The empty set is the no-match
// case; the others cover a single match, several distinct end ticks, and ties
// on the earliest end tick — the shapes §16.9.8 first_match reduces.
const std::vector<std::vector<uint32_t>>& OperandMatchSets() {
  static const std::vector<std::vector<uint32_t>> kSets = {
      {}, {7}, {5, 3, 4, 2}, {4, 4, 6}, {3, 3, 3},
  };
  return kSets;
}

// §16.12.2: strong(sequence_expr) is equivalent to
// strong(first_match(sequence_expr)) because a nonempty match of the sequence
// exists exactly when one exists for its first_match. Rather than assert this
// by an identity, drive the operand match set through the real §16.9.8
// first_match reduction (EvalFirstMatch) and confirm the strong verdict is
// unchanged: strong holds iff the operand had any match, and first_match
// preserves that existence.
TEST(SequenceProperty, StrongEqualsStrongOfFirstMatch) {
  for (const auto& match_set : OperandMatchSets()) {
    bool seq_has_match = !match_set.empty();
    bool first_match_has_match = EvalFirstMatch(match_set).matched;
    EXPECT_EQ(EvalStrongSequenceProperty(seq_has_match),
              EvalStrongSequenceProperty(first_match_has_match));
  }
}

// §16.12.2: weak(sequence_expr) is equivalent to
// weak(first_match(sequence_expr)) because a finite prefix witnesses inability
// to match the sequence exactly when it does for its first_match. Model the
// witness as the absence of any match over the observed word, and derive the
// first_match side through the real EvalFirstMatch reduction: because
// first_match keeps a match exactly when the operand had one, the two inability
// observations agree and the weak verdict is the same.
TEST(SequenceProperty, WeakEqualsWeakOfFirstMatch) {
  for (const auto& match_set : OperandMatchSets()) {
    bool seq_prefix_inability = match_set.empty();
    bool first_match_prefix_inability = !EvalFirstMatch(match_set).matched;
    EXPECT_EQ(EvalWeakSequenceProperty(seq_prefix_inability),
              EvalWeakSequenceProperty(first_match_prefix_inability));
  }
}

// --- Live cases: sequential properties over real source ---

// The module the cases share: clk rises at 5, 15, 25 and 35, tick n at
// 10n - 5, the tick counter counting through; b is high at ticks 2 to 4 and
// c at 3, so b ##1 c matches from tick 2 alone, the attempt from 1 has no
// match from its first tick, the one from 3 none from its second, and the
// one from 4 is still in flight when the run ends; `items` declare the
// assertions, counting in `passes` and `fails`.
std::string SequencePropertySource(const std::string& items) {
  return "module t;\n"
         "  logic clk = 0;\n"
         "  int tick = 1;\n"
         "  logic b, c;\n"
         "  int passes = 0;\n"
         "  int fails = 0;\n"
         "  always #5 clk = ~clk;\n"
         "  always #10 tick = tick + 1;\n"
         "  assign b = tick inside {2, 3, 4};\n"
         "  assign c = tick inside {3};\n" +
         items +
         "  initial #40 $finish;\n"
         "endmodule\n";
}

// §16.12.2: a sequence_expr in an assert is evaluated as weak(sequence_expr),
// true unless a finite prefix witnesses that the sequence cannot match: the
// attempt from 2 passes at 3, those from 1 and 3 fail at 1 and 4, and the
// one from 4, unfinished when the run ends, neither passes nor fails.
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

// §16.12.2: strong(sequence_expr) is true if and only if there is a nonempty
// match, so the attempt from 4, unfinished when the run ends, fails then as
// well, in the final blocks the run ends with: one pass, two failures at
// ticks and a third at the end.
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

// §16.12.2: weak(sequence_expr) written out is the bare form of an assert.
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

// §16.12.2: a sequence_expr in a cover is evaluated as strong, the pass
// statement running once per match: once, at 3.
TEST(SequenceProperty, BareSequenceInCoverIsStrong) {
  SimFixture f;
  auto* passes = RunAndFindVar(
      SequencePropertySource(
          "  c: cover property (@(posedge clk) b ##1 c) passes++;\n"),
      f, "passes");
  ASSERT_NE(passes, nullptr);
  EXPECT_EQ(passes->value.ToUint64(), 1u);
}

}  // namespace
