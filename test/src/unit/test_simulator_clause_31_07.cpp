#include "common/types.h"
#include "fixture_simulator.h"
#include "simulator/lowerer.h"
#include "simulator/specify.h"
#include "simulator/variable.h"

#include <gtest/gtest.h>

using namespace delta;

namespace {

constexpr Logic4Word kBit0{ 0, 0};
constexpr Logic4Word kBit1{ 1, 0};
constexpr Logic4Word kBitX{ 0, 1};

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

TEST(TimingCheckCondition, NondeterministicOperatorsClassifyAsNondeterministic) {
  EXPECT_FALSE(IsDeterministicTimingCheckCondition(
      TimingCheckConditionKind::kEq));
  EXPECT_FALSE(IsDeterministicTimingCheckCondition(
      TimingCheckConditionKind::kNeq));
}

TEST(TimingCheckCondition, PlainConditionEnablesOnOneDisablesOnZero) {
  EXPECT_TRUE(TimingCheckConditionEnables(
      TimingCheckConditionKind::kPlain, kBit1, 0));
  EXPECT_FALSE(TimingCheckConditionEnables(
      TimingCheckConditionKind::kPlain, kBit0, 0));
}

TEST(TimingCheckCondition, PlainConditionDisablesOnX) {
  EXPECT_FALSE(TimingCheckConditionEnables(
      TimingCheckConditionKind::kPlain, kBitX, 0));
}

TEST(TimingCheckCondition, NegateConditionEnablesOnZeroDisablesOnOne) {
  EXPECT_TRUE(TimingCheckConditionEnables(
      TimingCheckConditionKind::kNegate, kBit0, 0));
  EXPECT_FALSE(TimingCheckConditionEnables(
      TimingCheckConditionKind::kNegate, kBit1, 0));
}

TEST(TimingCheckCondition, EqConditionMatchesScalarConstant) {
  EXPECT_TRUE(TimingCheckConditionEnables(
      TimingCheckConditionKind::kEq, kBit0, 0));
  EXPECT_FALSE(TimingCheckConditionEnables(
      TimingCheckConditionKind::kEq, kBit1, 0));
  EXPECT_TRUE(TimingCheckConditionEnables(
      TimingCheckConditionKind::kEq, kBit1, 1));
  EXPECT_FALSE(TimingCheckConditionEnables(
      TimingCheckConditionKind::kEq, kBit0, 1));
}

TEST(TimingCheckCondition, EqConditionEnablesOnX) {
  EXPECT_TRUE(TimingCheckConditionEnables(
      TimingCheckConditionKind::kEq, kBitX, 0));
  EXPECT_TRUE(TimingCheckConditionEnables(
      TimingCheckConditionKind::kEq, kBitX, 1));
}

TEST(TimingCheckCondition, NeqConditionDiffersFromScalarConstant) {
  EXPECT_TRUE(TimingCheckConditionEnables(
      TimingCheckConditionKind::kNeq, kBit0, 1));
  EXPECT_FALSE(TimingCheckConditionEnables(
      TimingCheckConditionKind::kNeq, kBit1, 1));
}

TEST(TimingCheckCondition, ConditionUsesOnlyLeastSignificantBit) {
  // A multibit conditioning value is reduced to its LSB before being tested,
  // so the upper bits never affect whether the check is enabled.
  constexpr Logic4Word kLsbZero{ 2, 0};  // ...10 -> LSB 0
  constexpr Logic4Word kLsbOne{ 3, 0};   // ...11 -> LSB 1
  EXPECT_FALSE(TimingCheckConditionEnables(
      TimingCheckConditionKind::kPlain, kLsbZero, 0));
  EXPECT_TRUE(TimingCheckConditionEnables(
      TimingCheckConditionKind::kPlain, kLsbOne, 0));
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

}
