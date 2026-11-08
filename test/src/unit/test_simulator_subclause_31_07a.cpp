#include <gtest/gtest.h>

#include "common/types.h"
#include "fixture_parser.h"
#include "fixture_simulator.h"
#include "helpers_parser_verify.h"
#include "simulator/lowerer.h"
#include "simulator/specify_timing_check.h"
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
  constexpr Logic4Word kLsbZero{2, 0};
  constexpr Logic4Word kLsbOne{3, 0};
  EXPECT_FALSE(TimingCheckConditionEnables(TimingCheckConditionKind::kPlain,
                                           kLsbZero, 0));
  EXPECT_TRUE(TimingCheckConditionEnables(TimingCheckConditionKind::kPlain,
                                          kLsbOne, 0));
}

TimingCheckConditionClass ClassifyRefCondition(const std::string& cond_src) {
  std::string src =
      "module m;\n"
      "specify\n"
      "  $setup(data, posedge clk &&& " +
      cond_src +
      ", 10);\n"
      "endspecify\n"
      "endmodule\n";
  ParseResult r = Parse(src);
  EXPECT_FALSE(r.has_errors);
  auto* tc = GetSoleTimingCheck(r);
  EXPECT_NE(tc, nullptr);
  if (tc == nullptr) return {};
  return ClassifyTimingCheckCondition(tc->ref_condition);
}

TEST(ConditionedTimingCheckClassification, BareSignalIsPlain) {
  EXPECT_EQ(ClassifyRefCondition("en").kind, TimingCheckConditionKind::kPlain);
}

TEST(ConditionedTimingCheckClassification, ParenthesizedSignalIsPlain) {
  EXPECT_EQ(ClassifyRefCondition("(en)").kind,
            TimingCheckConditionKind::kPlain);
}

TEST(ConditionedTimingCheckClassification, TildeIsNegate) {
  EXPECT_EQ(ClassifyRefCondition("~reset").kind,
            TimingCheckConditionKind::kNegate);
}

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
  EXPECT_EQ(ClassifyTimingCheckCondition(nullptr).kind,
            TimingCheckConditionKind::kPlain);
}

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

TEST(ConditionedTimingCheckClassification, BareComparisonClassifies) {
  auto c = ClassifyRefCondition("en == 1'b1");
  EXPECT_EQ(c.kind, TimingCheckConditionKind::kEq);
  EXPECT_EQ(c.scalar_constant_bit, 1u);
}

TEST(ConditionedTimingCheckClassification, ParenthesizedNegateClassifies) {
  EXPECT_EQ(ClassifyRefCondition("(~clr)").kind,
            TimingCheckConditionKind::kNegate);
}

TEST(ConditionedTimingCheckClassification,
     EqualityAcceptsCapitalBSizedConstants) {
  auto one = ClassifyRefCondition("(en == 1'B1)");
  EXPECT_EQ(one.kind, TimingCheckConditionKind::kEq);
  EXPECT_EQ(one.scalar_constant_bit, 1u);
  auto zero = ClassifyRefCondition("(en == 1'B0)");
  EXPECT_EQ(zero.kind, TimingCheckConditionKind::kEq);
  EXPECT_EQ(zero.scalar_constant_bit, 0u);
}

TEST(ConditionedTimingCheckClassification,
     EqualityAcceptsCapitalBUnsizedConstants) {
  auto one = ClassifyRefCondition("(en == 'B1)");
  EXPECT_EQ(one.kind, TimingCheckConditionKind::kEq);
  EXPECT_EQ(one.scalar_constant_bit, 1u);
  auto zero = ClassifyRefCondition("(en == 'B0)");
  EXPECT_EQ(zero.kind, TimingCheckConditionKind::kEq);
  EXPECT_EQ(zero.scalar_constant_bit, 0u);
}

TEST(ConditionedTimingCheckClassification, EqualityAcceptsUnsizedZeroConstant) {
  auto c = ClassifyRefCondition("(en == 'b0)");
  EXPECT_EQ(c.kind, TimingCheckConditionKind::kEq);
  EXPECT_EQ(c.scalar_constant_bit, 0u);
}

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
  auto* var = RunAndFindVar(
      "module t;\n"
      "  logic [7:0] x;\n"
      "  specify\n"
      "    $setup(data, posedge clk &&& en, 10);\n"
      "  endspecify\n"
      "  initial x = 8'd33;\n"
      "endmodule\n",
      f, "x");
  ASSERT_NE(var, nullptr);
  EXPECT_EQ(var->value.ToUint64(), 33u);
}

}  // namespace
