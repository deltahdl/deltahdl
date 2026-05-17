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

TEST(TimingCheckCondition, NegateConditionDisablesOnX) {
  EXPECT_FALSE(TimingCheckConditionEnables(
      TimingCheckConditionKind::kNegate, kBitX, 0));
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

TEST(TimingCheckCondition, CaseEqConditionMatchesScalarConstant) {
  EXPECT_TRUE(TimingCheckConditionEnables(
      TimingCheckConditionKind::kCaseEq, kBit1, 1));
  EXPECT_FALSE(TimingCheckConditionEnables(
      TimingCheckConditionKind::kCaseEq, kBit0, 1));
}

TEST(TimingCheckCondition, CaseEqConditionDisablesOnX) {
  EXPECT_FALSE(TimingCheckConditionEnables(
      TimingCheckConditionKind::kCaseEq, kBitX, 0));
  EXPECT_FALSE(TimingCheckConditionEnables(
      TimingCheckConditionKind::kCaseEq, kBitX, 1));
}

TEST(TimingCheckCondition, NeqConditionDiffersFromScalarConstant) {
  EXPECT_TRUE(TimingCheckConditionEnables(
      TimingCheckConditionKind::kNeq, kBit0, 1));
  EXPECT_FALSE(TimingCheckConditionEnables(
      TimingCheckConditionKind::kNeq, kBit1, 1));
}

TEST(TimingCheckCondition, NeqConditionEnablesOnX) {
  EXPECT_TRUE(TimingCheckConditionEnables(
      TimingCheckConditionKind::kNeq, kBitX, 0));
  EXPECT_TRUE(TimingCheckConditionEnables(
      TimingCheckConditionKind::kNeq, kBitX, 1));
}

TEST(TimingCheckCondition, CaseNeqConditionDiffersFromScalarConstant) {
  EXPECT_TRUE(TimingCheckConditionEnables(
      TimingCheckConditionKind::kCaseNeq, kBit0, 1));
  EXPECT_FALSE(TimingCheckConditionEnables(
      TimingCheckConditionKind::kCaseNeq, kBit1, 1));
}

TEST(TimingCheckCondition, CaseNeqConditionDisablesOnX) {
  EXPECT_FALSE(TimingCheckConditionEnables(
      TimingCheckConditionKind::kCaseNeq, kBitX, 0));
  EXPECT_FALSE(TimingCheckConditionEnables(
      TimingCheckConditionKind::kCaseNeq, kBitX, 1));
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

}
