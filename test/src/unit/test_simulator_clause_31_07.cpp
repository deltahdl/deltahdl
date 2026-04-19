#include "common/types.h"
#include "fixture_simulator.h"
#include "simulator/lowerer.h"
#include "simulator/specify.h"
#include "simulator/variable.h"

#include <gtest/gtest.h>

using namespace delta;

namespace {

// Single-bit Logic4Word literals for the three logic states that §31.7
// directly addresses, so the enablement-decision tests below can spell
// the LSB of the conditioning signal explicitly without replicating the
// dual-rail encoding each time.
constexpr Logic4Word kBit0{/*aval=*/0, /*bval=*/0};
constexpr Logic4Word kBit1{/*aval=*/1, /*bval=*/0};
constexpr Logic4Word kBitX{/*aval=*/0, /*bval=*/1};

// §31.7: the four operator forms that the LRM labels as deterministic
// (no-op plain expression, bitwise/logical negation, case-equality, and
// case-inequality) classify as deterministic, which is the side that
// refuses to enable a timing check when the conditioning signal is x.
TEST(TimingCheckCondition, DeterministicOperatorsClassifyAsDeterministic) {
  EXPECT_TRUE(IsDeterministicTimingCheckCondition(
      TimingCheckConditionKind::kPlain));
  EXPECT_TRUE(IsDeterministicTimingCheckCondition(
      TimingCheckConditionKind::kNegate));
  EXPECT_TRUE(IsDeterministicTimingCheckCondition(
      TimingCheckConditionKind::kCaseEq));
  EXPECT_TRUE(IsDeterministicTimingCheckCondition(
      TimingCheckConditionKind::kCaseNeq));
}

// §31.7: the equality and inequality operators are explicitly labelled
// nondeterministic, which is the side that enables a timing check even
// when the conditioning signal is x.
TEST(TimingCheckCondition, NondeterministicOperatorsClassifyAsNondeterministic) {
  EXPECT_FALSE(IsDeterministicTimingCheckCondition(
      TimingCheckConditionKind::kEq));
  EXPECT_FALSE(IsDeterministicTimingCheckCondition(
      TimingCheckConditionKind::kNeq));
}

// §31.7 Example 1 (first form): a plain-expression condition such as
// `$setup(data, posedge clk &&& clr, 10)` enables only when the
// conditioning signal's LSB is a known 1.
TEST(TimingCheckCondition, PlainConditionEnablesOnOneDisablesOnZero) {
  EXPECT_TRUE(TimingCheckConditionEnables(
      TimingCheckConditionKind::kPlain, kBit1, /*scalar_constant_bit=*/0));
  EXPECT_FALSE(TimingCheckConditionEnables(
      TimingCheckConditionKind::kPlain, kBit0, /*scalar_constant_bit=*/0));
}

// §31.7: a plain-expression condition is deterministic, so an x-valued
// conditioning signal must not enable the timing check even though a
// naive truthiness test on x could go either way.
TEST(TimingCheckCondition, PlainConditionDisablesOnX) {
  EXPECT_FALSE(TimingCheckConditionEnables(
      TimingCheckConditionKind::kPlain, kBitX, /*scalar_constant_bit=*/0));
}

// §31.7 Example 2 (first form): `&&& (~clr)` inverts the conditioning
// signal. The condition enables on a known 0 and disables on a known 1.
TEST(TimingCheckCondition, NegateConditionEnablesOnZeroDisablesOnOne) {
  EXPECT_TRUE(TimingCheckConditionEnables(
      TimingCheckConditionKind::kNegate, kBit0, /*scalar_constant_bit=*/0));
  EXPECT_FALSE(TimingCheckConditionEnables(
      TimingCheckConditionKind::kNegate, kBit1, /*scalar_constant_bit=*/0));
}

// §31.7: the negation form is deterministic, so an x-valued conditioning
// signal must not enable the check.
TEST(TimingCheckCondition, NegateConditionDisablesOnX) {
  EXPECT_FALSE(TimingCheckConditionEnables(
      TimingCheckConditionKind::kNegate, kBitX, /*scalar_constant_bit=*/0));
}

// §31.7 Example 2 (second form): `&&& (clr==0)` is nondeterministic
// equality. Enables iff the LSB matches the scalar_constant bit.
TEST(TimingCheckCondition, EqConditionMatchesScalarConstant) {
  EXPECT_TRUE(TimingCheckConditionEnables(
      TimingCheckConditionKind::kEq, kBit0, /*scalar_constant_bit=*/0));
  EXPECT_FALSE(TimingCheckConditionEnables(
      TimingCheckConditionKind::kEq, kBit1, /*scalar_constant_bit=*/0));
  EXPECT_TRUE(TimingCheckConditionEnables(
      TimingCheckConditionKind::kEq, kBit1, /*scalar_constant_bit=*/1));
  EXPECT_FALSE(TimingCheckConditionEnables(
      TimingCheckConditionKind::kEq, kBit0, /*scalar_constant_bit=*/1));
}

// §31.7: the `==` form is nondeterministic, so an x-valued conditioning
// signal must enable the check regardless of the scalar_constant bit.
TEST(TimingCheckCondition, EqConditionEnablesOnX) {
  EXPECT_TRUE(TimingCheckConditionEnables(
      TimingCheckConditionKind::kEq, kBitX, /*scalar_constant_bit=*/0));
  EXPECT_TRUE(TimingCheckConditionEnables(
      TimingCheckConditionKind::kEq, kBitX, /*scalar_constant_bit=*/1));
}

// §31.7: `expr === scalar_constant` is deterministic equality. On known
// values it mirrors the `==` case; on x it refuses to enable.
TEST(TimingCheckCondition, CaseEqConditionMatchesScalarConstant) {
  EXPECT_TRUE(TimingCheckConditionEnables(
      TimingCheckConditionKind::kCaseEq, kBit1, /*scalar_constant_bit=*/1));
  EXPECT_FALSE(TimingCheckConditionEnables(
      TimingCheckConditionKind::kCaseEq, kBit0, /*scalar_constant_bit=*/1));
}

TEST(TimingCheckCondition, CaseEqConditionDisablesOnX) {
  EXPECT_FALSE(TimingCheckConditionEnables(
      TimingCheckConditionKind::kCaseEq, kBitX, /*scalar_constant_bit=*/0));
  EXPECT_FALSE(TimingCheckConditionEnables(
      TimingCheckConditionKind::kCaseEq, kBitX, /*scalar_constant_bit=*/1));
}

// §31.7: `expr != scalar_constant` is nondeterministic inequality.
TEST(TimingCheckCondition, NeqConditionDiffersFromScalarConstant) {
  EXPECT_TRUE(TimingCheckConditionEnables(
      TimingCheckConditionKind::kNeq, kBit0, /*scalar_constant_bit=*/1));
  EXPECT_FALSE(TimingCheckConditionEnables(
      TimingCheckConditionKind::kNeq, kBit1, /*scalar_constant_bit=*/1));
}

TEST(TimingCheckCondition, NeqConditionEnablesOnX) {
  EXPECT_TRUE(TimingCheckConditionEnables(
      TimingCheckConditionKind::kNeq, kBitX, /*scalar_constant_bit=*/0));
  EXPECT_TRUE(TimingCheckConditionEnables(
      TimingCheckConditionKind::kNeq, kBitX, /*scalar_constant_bit=*/1));
}

// §31.7: `expr !== scalar_constant` is deterministic inequality.
TEST(TimingCheckCondition, CaseNeqConditionDiffersFromScalarConstant) {
  EXPECT_TRUE(TimingCheckConditionEnables(
      TimingCheckConditionKind::kCaseNeq, kBit0, /*scalar_constant_bit=*/1));
  EXPECT_FALSE(TimingCheckConditionEnables(
      TimingCheckConditionKind::kCaseNeq, kBit1, /*scalar_constant_bit=*/1));
}

TEST(TimingCheckCondition, CaseNeqConditionDisablesOnX) {
  EXPECT_FALSE(TimingCheckConditionEnables(
      TimingCheckConditionKind::kCaseNeq, kBitX, /*scalar_constant_bit=*/0));
  EXPECT_FALSE(TimingCheckConditionEnables(
      TimingCheckConditionKind::kCaseNeq, kBitX, /*scalar_constant_bit=*/1));
}

// §31.7 Syntax 31-16: a plain-expression `&&&` condition drives the full
// source→runtime pipeline without error so that downstream modules continue
// to initialise.
TEST(ConditionedTimingCheckSimulation, TimingCheckConditionSimulates) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "module t;\n"
      "  logic [7:0] x;\n"
      "  specify\n"
      "    $setup(data &&& en, posedge clk, 10);\n"
      "  endspecify\n"
      "  initial x = 8'd33;\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  Lowerer lowerer(f.ctx, f.arena, f.diag);
  lowerer.Lower(design);
  f.scheduler.Run();
  auto* var = f.ctx.FindVariable("x");
  ASSERT_NE(var, nullptr);
  EXPECT_EQ(var->value.ToUint64(), 33u);
}

// §31.7 Syntax 31-16: conditions on both timing_check_event operands
// survive end-to-end elaboration and simulation.
TEST(ConditionedTimingCheckSimulation, ConditionBothEventsSimulates) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "module t;\n"
      "  logic [7:0] x;\n"
      "  specify\n"
      "    $hold(posedge clk &&& en, data &&& reset, 5);\n"
      "  endspecify\n"
      "  initial x = 8'd66;\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  Lowerer lowerer(f.ctx, f.arena, f.diag);
  lowerer.Lower(design);
  f.scheduler.Run();
  auto* var = f.ctx.FindVariable("x");
  ASSERT_NE(var, nullptr);
  EXPECT_EQ(var->value.ToUint64(), 66u);
}

// §31.7 Syntax 31-16: the `~ expression` condition form survives end-to-end
// elaboration and simulation.
TEST(ConditionedTimingCheckSimulation, TimingCheckConditionNegationSimulates) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "module t;\n"
      "  logic [7:0] x;\n"
      "  specify\n"
      "    $setup(data &&& ~reset, posedge clk, 10);\n"
      "  endspecify\n"
      "  initial x = 8'd22;\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  Lowerer lowerer(f.ctx, f.arena, f.diag);
  lowerer.Lower(design);
  f.scheduler.Run();
  auto* var = f.ctx.FindVariable("x");
  ASSERT_NE(var, nullptr);
  EXPECT_EQ(var->value.ToUint64(), 22u);
}

// §31.7 Syntax 31-16: an `expression == scalar_constant` condition survives
// end-to-end elaboration and simulation, covering the equality path that
// the plain/negated forms do not exercise.
TEST(ConditionedTimingCheckSimulation, EqualityConditionSimulates) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "module t;\n"
      "  logic [7:0] x;\n"
      "  specify\n"
      "    $setup(data &&& (en == 1'b1), posedge clk, 10);\n"
      "  endspecify\n"
      "  initial x = 8'd44;\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  Lowerer lowerer(f.ctx, f.arena, f.diag);
  lowerer.Lower(design);
  f.scheduler.Run();
  auto* var = f.ctx.FindVariable("x");
  ASSERT_NE(var, nullptr);
  EXPECT_EQ(var->value.ToUint64(), 44u);
}

// §31.7: when the conditioning value is a multibit signal only its LSB is
// consulted. The pipeline must accept such a signal without dropping the
// surrounding design on the floor.
TEST(ConditionedTimingCheckSimulation, MultibitConditioningSignalSimulates) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "module t;\n"
      "  logic [7:0] x;\n"
      "  logic [3:0] en;\n"
      "  specify\n"
      "    $setup(data &&& en, posedge clk, 10);\n"
      "  endspecify\n"
      "  initial x = 8'd55;\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  Lowerer lowerer(f.ctx, f.arena, f.diag);
  lowerer.Lower(design);
  f.scheduler.Run();
  auto* var = f.ctx.FindVariable("x");
  ASSERT_NE(var, nullptr);
  EXPECT_EQ(var->value.ToUint64(), 55u);
}

}  // namespace
