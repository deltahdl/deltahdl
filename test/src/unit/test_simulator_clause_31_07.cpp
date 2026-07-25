#include <gtest/gtest.h>

#include "common/types.h"
#include "fixture_simulator.h"
#include "helpers_parser_verify.h"
#include "simulator/lowerer.h"
#include "simulator/specify.h"
#include "simulator/variable.h"

using namespace delta;

namespace {

constexpr Logic4Word kBit0{0, 0};
constexpr Logic4Word kBit1{1, 0};
constexpr Logic4Word kBitX{0, 1};

TEST(TimingCheckCondition, DeterministicOperatorsClassifyAsDeterministic) {
  EXPECT_TRUE(
      IsDeterministicTimingCheckCondition(TimingCheckConditionKind::kPlain));
  EXPECT_TRUE(
      IsDeterministicTimingCheckCondition(TimingCheckConditionKind::kNegate));
  EXPECT_TRUE(
      IsDeterministicTimingCheckCondition(TimingCheckConditionKind::kCaseEq));
  EXPECT_TRUE(
      IsDeterministicTimingCheckCondition(TimingCheckConditionKind::kCaseNeq));
}

TEST(TimingCheckCondition,
     NondeterministicOperatorsClassifyAsNondeterministic) {
  EXPECT_FALSE(
      IsDeterministicTimingCheckCondition(TimingCheckConditionKind::kEq));
  EXPECT_FALSE(
      IsDeterministicTimingCheckCondition(TimingCheckConditionKind::kNeq));
}

TEST(TimingCheckCondition, PlainConditionEnablesOnOneDisablesOnZero) {
  EXPECT_TRUE(
      TimingCheckConditionEnables(TimingCheckConditionKind::kPlain, kBit1, 0));
  EXPECT_FALSE(
      TimingCheckConditionEnables(TimingCheckConditionKind::kPlain, kBit0, 0));
}

TEST(TimingCheckCondition, PlainConditionDisablesOnX) {
  EXPECT_FALSE(
      TimingCheckConditionEnables(TimingCheckConditionKind::kPlain, kBitX, 0));
}

TEST(TimingCheckCondition, NegateConditionEnablesOnZeroDisablesOnOne) {
  EXPECT_TRUE(
      TimingCheckConditionEnables(TimingCheckConditionKind::kNegate, kBit0, 0));
  EXPECT_FALSE(
      TimingCheckConditionEnables(TimingCheckConditionKind::kNegate, kBit1, 0));
}

TEST(TimingCheckCondition, EqConditionMatchesScalarConstant) {
  EXPECT_TRUE(
      TimingCheckConditionEnables(TimingCheckConditionKind::kEq, kBit0, 0));
  EXPECT_FALSE(
      TimingCheckConditionEnables(TimingCheckConditionKind::kEq, kBit1, 0));
  EXPECT_TRUE(
      TimingCheckConditionEnables(TimingCheckConditionKind::kEq, kBit1, 1));
  EXPECT_FALSE(
      TimingCheckConditionEnables(TimingCheckConditionKind::kEq, kBit0, 1));
}

TEST(TimingCheckCondition, EqConditionEnablesOnX) {
  EXPECT_TRUE(
      TimingCheckConditionEnables(TimingCheckConditionKind::kEq, kBitX, 0));
  EXPECT_TRUE(
      TimingCheckConditionEnables(TimingCheckConditionKind::kEq, kBitX, 1));
}

TEST(TimingCheckCondition, NeqConditionDiffersFromScalarConstant) {
  EXPECT_TRUE(
      TimingCheckConditionEnables(TimingCheckConditionKind::kNeq, kBit0, 1));
  EXPECT_FALSE(
      TimingCheckConditionEnables(TimingCheckConditionKind::kNeq, kBit1, 1));
}

TEST(TimingCheckCondition, ConditionUsesOnlyLeastSignificantBit) {
  // A multibit conditioning value is reduced to its LSB before being tested,
  // so the upper bits never affect whether the check is enabled.
  constexpr Logic4Word kLsbZero{2, 0};  // ...10 -> LSB 0
  constexpr Logic4Word kLsbOne{3, 0};   // ...11 -> LSB 1
  EXPECT_FALSE(TimingCheckConditionEnables(TimingCheckConditionKind::kPlain,
                                           kLsbZero, 0));
  EXPECT_TRUE(TimingCheckConditionEnables(TimingCheckConditionKind::kPlain,
                                          kLsbOne, 0));
}

// Parse a module carrying a single conditioned timing check and run the parsed
// reference-event `&&&` condition through the production classifier, returning
// the small result POD. The ParseResult (and its arena) stays alive across the
// ClassifyTimingCheckCondition call, so the classifier observes the expression
// exactly as the parser built it from real syntax -- not a hand-built AST.
TimingCheckConditionClass ClassifyRefCondition(const std::string& cond_src) {
  std::string src =
      "module m;\n"
      "specify\n"
      "  $setup(data &&& " +
      cond_src +
      ", posedge clk, 10);\n"
      "endspecify\n"
      "endmodule\n";
  ParseResult r = Parse(src);
  EXPECT_FALSE(r.has_errors);
  auto* tc = GetSoleTimingCheck(r);
  EXPECT_NE(tc, nullptr);
  if (tc == nullptr) return {};
  return ClassifyTimingCheckCondition(tc->ref_condition);
}

// §31.7: a bare conditioning signal parses to the plain scalar_timing_check_
// condition form. The classifier recovers that from the parsed expression.
TEST(ConditionedTimingCheckClassification, BareSignalIsPlain) {
  EXPECT_EQ(ClassifyRefCondition("en").kind, TimingCheckConditionKind::kPlain);
}

TEST(ConditionedTimingCheckClassification, ParenthesizedSignalIsPlain) {
  EXPECT_EQ(ClassifyRefCondition("(en)").kind,
            TimingCheckConditionKind::kPlain);
}

// §31.7: `~ expression` is the deterministic negate form.
TEST(ConditionedTimingCheckClassification, TildeIsNegate) {
  EXPECT_EQ(ClassifyRefCondition("~reset").kind,
            TimingCheckConditionKind::kNegate);
}

// §31.7: the four comparison forms map to their kinds and carry the LSB of the
// scalar_constant operand -- derived here from the real parsed literal.
TEST(ConditionedTimingCheckClassification, EqualityCarriesConstantBit) {
  auto c0 = ClassifyRefCondition("(en == 1'b0)");
  EXPECT_EQ(c0.kind, TimingCheckConditionKind::kEq);
  EXPECT_EQ(c0.scalar_constant_bit, 0u);
  auto c1 = ClassifyRefCondition("(en == 1'b1)");
  EXPECT_EQ(c1.kind, TimingCheckConditionKind::kEq);
  EXPECT_EQ(c1.scalar_constant_bit, 1u);
}

TEST(ConditionedTimingCheckClassification, CaseEqualityIsCaseEq) {
  auto c = ClassifyRefCondition("(en === 1'b1)");
  EXPECT_EQ(c.kind, TimingCheckConditionKind::kCaseEq);
  EXPECT_EQ(c.scalar_constant_bit, 1u);
}

TEST(ConditionedTimingCheckClassification, InequalityIsNeq) {
  auto c = ClassifyRefCondition("(mode != 1'b0)");
  EXPECT_EQ(c.kind, TimingCheckConditionKind::kNeq);
  EXPECT_EQ(c.scalar_constant_bit, 0u);
}

TEST(ConditionedTimingCheckClassification, CaseInequalityIsCaseNeq) {
  auto c = ClassifyRefCondition("(mode !== 1'b0)");
  EXPECT_EQ(c.kind, TimingCheckConditionKind::kCaseNeq);
  EXPECT_EQ(c.scalar_constant_bit, 0u);
}

TEST(ConditionedTimingCheckClassification, NullConditionIsPlain) {
  // An unconditioned event (no `&&&`) presents a null condition expression.
  EXPECT_EQ(ClassifyTimingCheckCondition(nullptr).kind,
            TimingCheckConditionKind::kPlain);
}

// §31.7 end-to-end from real syntax: the operator chosen in the parsed `&&&`
// clause decides whether an x on the conditioning signal enables the check.
// A deterministic comparison (===) built from source shall disable on x; a
// nondeterministic comparison (==) built from source shall enable on x. The
// classifier and the enable predicate are chained exactly as production code
// would, so the whole rule is observed on parsed input.
TEST(ConditionedTimingCheckClassification, DeterministicSyntaxDisablesOnX) {
  auto c = ClassifyRefCondition("(en === 1'b1)");
  EXPECT_TRUE(IsDeterministicTimingCheckCondition(c.kind));
  EXPECT_FALSE(
      TimingCheckConditionEnables(c.kind, kBitX, c.scalar_constant_bit));
  EXPECT_TRUE(
      TimingCheckConditionEnables(c.kind, kBit1, c.scalar_constant_bit));
  EXPECT_FALSE(
      TimingCheckConditionEnables(c.kind, kBit0, c.scalar_constant_bit));
}

TEST(ConditionedTimingCheckClassification, NondeterministicSyntaxEnablesOnX) {
  auto c = ClassifyRefCondition("(en == 1'b1)");
  EXPECT_FALSE(IsDeterministicTimingCheckCondition(c.kind));
  EXPECT_TRUE(
      TimingCheckConditionEnables(c.kind, kBitX, c.scalar_constant_bit));
  EXPECT_TRUE(
      TimingCheckConditionEnables(c.kind, kBit1, c.scalar_constant_bit));
  EXPECT_FALSE(
      TimingCheckConditionEnables(c.kind, kBit0, c.scalar_constant_bit));
}

// §31.7: the scalar_constant production admits the bare decimal 1/0 and the
// unsized-base 'b1/'b0 spellings, not just the sized 1'b1/1'b0 forms. Built
// from real source, each still classifies as the equality form and carries the
// matching constant bit.
TEST(ConditionedTimingCheckClassification,
     EqualityAcceptsBareAndUnsizedConstants) {
  auto one = ClassifyRefCondition("(en == 1)");
  EXPECT_EQ(one.kind, TimingCheckConditionKind::kEq);
  EXPECT_EQ(one.scalar_constant_bit, 1u);
  auto zero = ClassifyRefCondition("(en == 0)");
  EXPECT_EQ(zero.kind, TimingCheckConditionKind::kEq);
  EXPECT_EQ(zero.scalar_constant_bit, 0u);
  auto unsized = ClassifyRefCondition("(en == 'b1)");
  EXPECT_EQ(unsized.kind, TimingCheckConditionKind::kEq);
  EXPECT_EQ(unsized.scalar_constant_bit, 1u);
}

// §31.7: a `&&&` condition can attach to the data event as well as the
// reference event; the data-position condition feeds the same classification.
// Build it from real $hold source and classify the parsed data_condition.
TEST(ConditionedTimingCheckClassification, DataPositionConditionClassifies) {
  ParseResult r = Parse(
      "module m;\n"
      "specify\n"
      "  $hold(posedge clk &&& en, data &&& (rst == 1'b0), 5);\n"
      "endspecify\n"
      "endmodule\n");
  ASSERT_FALSE(r.has_errors);
  auto* tc = GetSoleTimingCheck(r);
  ASSERT_NE(tc, nullptr);
  auto c = ClassifyTimingCheckCondition(tc->data_condition);
  EXPECT_EQ(c.kind, TimingCheckConditionKind::kEq);
  EXPECT_EQ(c.scalar_constant_bit, 0u);
}

// §31.7: the comparison form need not be parenthesized. A bare
// `expression == scalar_constant` built from source classifies as the equality
// kind, exactly like its parenthesized twin.
TEST(ConditionedTimingCheckClassification, BareComparisonClassifies) {
  auto c = ClassifyRefCondition("en == 1'b1");
  EXPECT_EQ(c.kind, TimingCheckConditionKind::kEq);
  EXPECT_EQ(c.scalar_constant_bit, 1u);
}

// §31.7: the `~` form wrapped in the parenthesized timing_check_condition
// production (as the LRM's own low-enable example spells it) still classifies
// as the deterministic negate form.
TEST(ConditionedTimingCheckClassification, ParenthesizedNegateClassifies) {
  EXPECT_EQ(ClassifyRefCondition("(~clr)").kind,
            TimingCheckConditionKind::kNegate);
}

// §31.7: scalar_constant also admits the upper-case-base spellings 1'B0/1'B1.
// Built from source, each yields the equality kind with the matching bit.
TEST(ConditionedTimingCheckClassification,
     EqualityAcceptsCapitalBSizedConstants) {
  auto one = ClassifyRefCondition("(en == 1'B1)");
  EXPECT_EQ(one.kind, TimingCheckConditionKind::kEq);
  EXPECT_EQ(one.scalar_constant_bit, 1u);
  auto zero = ClassifyRefCondition("(en == 1'B0)");
  EXPECT_EQ(zero.kind, TimingCheckConditionKind::kEq);
  EXPECT_EQ(zero.scalar_constant_bit, 0u);
}

// §31.7: scalar_constant admits the unsized upper-case-base spellings 'B0/'B1.
TEST(ConditionedTimingCheckClassification,
     EqualityAcceptsCapitalBUnsizedConstants) {
  auto one = ClassifyRefCondition("(en == 'B1)");
  EXPECT_EQ(one.kind, TimingCheckConditionKind::kEq);
  EXPECT_EQ(one.scalar_constant_bit, 1u);
  auto zero = ClassifyRefCondition("(en == 'B0)");
  EXPECT_EQ(zero.kind, TimingCheckConditionKind::kEq);
  EXPECT_EQ(zero.scalar_constant_bit, 0u);
}

// §31.7: the unsized lower-case-base zero 'b0 completes the scalar_constant
// spelling coverage.
TEST(ConditionedTimingCheckClassification, EqualityAcceptsUnsizedZeroConstant) {
  auto c = ClassifyRefCondition("(en == 'b0)");
  EXPECT_EQ(c.kind, TimingCheckConditionKind::kEq);
  EXPECT_EQ(c.scalar_constant_bit, 0u);
}

// §31.7 end-to-end over a §31.4.4 $width check (a single-signal timing check)
// with a §31.5 negedge reference: the `&&&` condition parses on a check whose
// argument shape differs from $setup, and the parsed condition still feeds the
// classifier. Built from real $width source, not a hand-made event.
TEST(ConditionedTimingCheckClassification,
     SingleSignalWidthCheckConditionClassifies) {
  ParseResult r = Parse(
      "module m;\n"
      "specify\n"
      "  $width(negedge clk &&& en, 5, 2, ntf);\n"
      "endspecify\n"
      "endmodule\n");
  ASSERT_FALSE(r.has_errors);
  auto* tc = GetSoleTimingCheck(r);
  ASSERT_NE(tc, nullptr);
  auto c = ClassifyTimingCheckCondition(tc->ref_condition);
  EXPECT_EQ(c.kind, TimingCheckConditionKind::kPlain);
}

// §31.7 end-to-end over a §31.4.5 $period check: a case-equality condition
// built from real $period source classifies as the deterministic case-eq form
// and carries the scalar_constant bit.
TEST(ConditionedTimingCheckClassification, PeriodCheckConditionClassifies) {
  ParseResult r = Parse(
      "module m;\n"
      "specify\n"
      "  $period(posedge clk &&& (en === 1'b1), 5, ntf);\n"
      "endspecify\n"
      "endmodule\n");
  ASSERT_FALSE(r.has_errors);
  auto* tc = GetSoleTimingCheck(r);
  ASSERT_NE(tc, nullptr);
  auto c = ClassifyTimingCheckCondition(tc->ref_condition);
  EXPECT_EQ(c.kind, TimingCheckConditionKind::kCaseEq);
  EXPECT_EQ(c.scalar_constant_bit, 1u);
}

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

}  // namespace
