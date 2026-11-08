#include <gtest/gtest.h>

#include <cstdint>
#include <string>

#include "common/types.h"
#include "fixture_simulator.h"
#include "simulator/sva_engine_sampling.h"

using namespace delta;

namespace {

TEST(ConcurrentAssertionSampling, StaticVariableSamplesPreponedAtNonzeroTime) {
  SampledValue sv = SampleStaticVariable(0x1234, SimTime{10}, 0);
  EXPECT_EQ(sv.value, 0x1234u);
  EXPECT_EQ(sv.mode, SampleMode::kPreponed);
}

TEST(ConcurrentAssertionSampling, StaticVariableSamplesDefaultAtTimeZero) {
  SampledValue sv = SampleStaticVariable(0xDEAD, SimTime{0}, 0);
  EXPECT_EQ(sv.value, 0u);
  EXPECT_EQ(sv.mode, SampleMode::kDefault);
}

TEST(ConcurrentAssertionSampling, AutomaticVariableSamplesCurrentValue) {
  SampledValue sv = SampleAutomaticVariable(0xABCD);
  EXPECT_EQ(sv.value, 0xABCDu);
  EXPECT_EQ(sv.mode, SampleMode::kCurrent);
}

TEST(ConcurrentAssertionSampling, LocalVariableSamplesCurrentValue) {
  SampledValue sv = SampleLocalVariable(0x2468);
  EXPECT_EQ(sv.value, 0x2468u);
  EXPECT_EQ(sv.mode, SampleMode::kCurrent);
}

TEST(ConcurrentAssertionSampling,
     StaticVariableDefaultIsDeclarationAssignedValue) {
  SampledValue sv = SampleStaticVariable(0xDEAD, SimTime{0}, 7);
  EXPECT_EQ(sv.value, 7u);
  EXPECT_EQ(sv.mode, SampleMode::kDefault);
}

TEST(ConcurrentAssertionSampling,
     ActiveFreeCheckerVariableSamplesCurrentValue) {
  SampledValue sv = SampleActiveFreeCheckerVariable(0x1357);
  EXPECT_EQ(sv.value, 0x1357u);
  EXPECT_EQ(sv.mode, SampleMode::kCurrent);
}

TEST(ConcurrentAssertionSampling, FreeCheckerPastFutureSamplesPostponedRegion) {
  SampledValue sv = SampleActiveFreeCheckerVarPastFuture(0x99);
  EXPECT_EQ(sv.value, 0x99u);
  EXPECT_EQ(sv.mode, SampleMode::kPostponed);
}

TEST(ConcurrentAssertionSampling, AutomaticPastFutureCollapsesToCurrentValue) {
  SampledValue sv = SampleAutomaticVarPastFuture(0x42);
  EXPECT_EQ(sv.value, 0x42u);
  EXPECT_EQ(sv.mode, SampleMode::kCurrent);
}

TEST(ConcurrentAssertionSampling, DefaultSampledValueOfTriggeredIsZero) {
  SampledValue t = DefaultSampledValueOfTriggered();
  EXPECT_EQ(t.value, 0u);
  SampledValue m = DefaultSampledValueOfMatched();
  EXPECT_EQ(m.value, 0u);
}

TEST(ConcurrentAssertionSampling,
     SingleVariableExpressionForwardsVariableSample) {
  SampledValue var = SampleStaticVariable(0x55, SimTime{5}, 0);
  SampledValue expr = SampleSingleVariableExpression(var);
  EXPECT_EQ(expr.value, var.value);
  EXPECT_EQ(expr.mode, var.mode);
}

TEST(ConcurrentAssertionSampling, ConstCastUsesCurrentValueOfArgument) {
  SampledValue sv = SampleConstCastExpression(0xBEEF);
  EXPECT_EQ(sv.value, 0xBEEFu);
  EXPECT_EQ(sv.mode, SampleMode::kCurrent);
}

TEST(ConcurrentAssertionSampling, TriggeredAndMatchedUseCurrentReturnedValue) {
  SampledValue t = SampledValueOfTriggered(true);
  EXPECT_EQ(t.value, 1u);
  EXPECT_EQ(t.mode, SampleMode::kCurrent);
  SampledValue m = SampledValueOfMatched(false);
  EXPECT_EQ(m.value, 0u);
  EXPECT_EQ(m.mode, SampleMode::kCurrent);
}

TEST(ConcurrentAssertionSampling, RecursiveExpressionBitwiseAndsSampledValues) {
  SampledValue a = SampleStaticVariable(0xF0F0, SimTime{1}, 0);
  SampledValue b = SampleStaticVariable(0x0FF0, SimTime{1}, 0);
  SampledValue combined = SampleRecursiveExpression(
      a, b, [](uint64_t x, uint64_t y) { return x & y; });
  EXPECT_EQ(combined.value, 0x00F0u);
  EXPECT_EQ(combined.mode, SampleMode::kPreponed);
}

TEST(ConcurrentAssertionSampling,
     RecursivePropagatesCurrentWhenSubexpressionCurrent) {
  SampledValue a = SampleStaticVariable(0x10, SimTime{1}, 0);
  SampledValue s_triggered = SampledValueOfTriggered(true);
  SampledValue combined = SampleRecursiveExpression(
      a, s_triggered, [](uint64_t x, uint64_t y) { return x | y; });
  EXPECT_EQ(combined.mode, SampleMode::kCurrent);
  EXPECT_EQ(combined.value, 0x11u);
}

TEST(ConcurrentAssertionSampling, OtherVariableOrNetDefaultIsTypeDefault) {
  SampledValue sv = DefaultSampledValueOfVariableOrNet(0);
  EXPECT_EQ(sv.value, 0u);
  EXPECT_EQ(sv.mode, SampleMode::kDefault);
}

TEST(ConcurrentAssertionSampling, DefaultSampledValueOfExpressionIsRecursive) {
  SampledValue a = DefaultSampledValueOfVariableOrNet(0xAA);
  SampledValue b = DefaultSampledValueOfVariableOrNet(0x55);
  SampledValue combined = SampleRecursiveExpression(
      a, b, [](uint64_t x, uint64_t y) { return x | y; });
  EXPECT_EQ(combined.value, 0xFFu);

  EXPECT_NE(combined.mode, SampleMode::kCurrent);
}

TEST(ConcurrentAssertionSampling, ClockingBlockInputMustUseStep1Sampling) {
  EXPECT_TRUE(IsClockingBlockInputSamplingValid(ClockingInputSkew::kStep1));
  EXPECT_FALSE(IsClockingBlockInputSamplingValid(ClockingInputSkew::kOther));
}

std::string SourceWithTickStep(const std::string& tick_line) {
  return "module m;\n"
         "  logic clk;\n"
         "  logic a;\n"
         "  int hits = 0;\n"
         "  int misses = 0;\n"
         "  assert property (@(posedge clk) a) hits = hits + 1;\n"
         "  else misses = misses + 1;\n"
         "  initial begin\n"
         "    clk = 1'b0; a = 1'b0;\n"
         "    #5 " +
         tick_line +
         "\n"
         "  end\n"
         "endmodule\n";
}

TEST(ConcurrentAssertionSampling, VerdictDoesNotDependOnWriteOrderInTheTick) {
  SimFixture before;
  auto* first_hits = RunAndFindVar(SourceWithTickStep("a = 1'b1; clk = 1'b1;"),
                                   before, "hits");
  ASSERT_NE(first_hits, nullptr);
  auto* first_misses = before.ctx.FindVariable("misses");
  ASSERT_NE(first_misses, nullptr);
  SimFixture after;
  auto* second_hits =
      RunAndFindVar(SourceWithTickStep("clk = 1'b1; a = 1'b1;"), after, "hits");
  ASSERT_NE(second_hits, nullptr);
  auto* second_misses = after.ctx.FindVariable("misses");
  ASSERT_NE(second_misses, nullptr);
  EXPECT_EQ(first_hits->value.ToUint64(), second_hits->value.ToUint64());
  EXPECT_EQ(first_misses->value.ToUint64(), second_misses->value.ToUint64());
  EXPECT_EQ(first_hits->value.ToUint64(), 0u);
  EXPECT_EQ(first_misses->value.ToUint64(), 1u);
}

TEST(ConcurrentAssertionSampling, TimeZeroTickReadsTheDefaultSampledValue) {
  SimFixture f;
  const std::string kSrc =
      "module m;\n"
      "  logic clk;\n"
      "  logic a;\n"
      "  int hits = 0;\n"
      "  int misses = 0;\n"
      "  assert property (@(posedge clk) a) hits = hits + 1;\n"
      "  else misses = misses + 1;\n"
      "  initial begin\n"
      "    a = 1'b1;\n"
      "    clk = 1'b0;\n"
      "    clk = 1'b1;\n"
      "  end\n"
      "endmodule\n";
  auto* hits = RunAndFindVar(kSrc, f, "hits");
  ASSERT_NE(hits, nullptr);
  EXPECT_EQ(hits->value.ToUint64(), 0u);
  auto* misses = f.ctx.FindVariable("misses");
  ASSERT_NE(misses, nullptr);
  EXPECT_EQ(misses->value.ToUint64(), 1u);
}

TEST(ConcurrentAssertionSampling, ChildInstanceOperandReadsThePreponedValue) {
  SimFixture f;
  auto* var = RunAndFindVar(
      "module leaf;\n"
      "  logic req = 0;\n"
      "endmodule\n"
      "module m;\n"
      "  logic clk = 0;\n"
      "  int hits = 0;\n"
      "  leaf u();\n"
      "  assert property (@(posedge clk) u.req) hits = hits + 1;\n"
      "  initial begin\n"
      "    #5 u.req = 1;\n"
      "    clk = 1;\n"
      "  end\n"
      "endmodule\n",
      f, "hits");
  ASSERT_NE(var, nullptr);
  EXPECT_EQ(var->value.ToUint64(), 0u);
}

TEST(ConcurrentAssertionSampling,
     ChildInstanceOperandSettledBeforeTheTickHolds) {
  SimFixture f;
  auto* var = RunAndFindVar(
      "module leaf;\n"
      "  logic req = 0;\n"
      "endmodule\n"
      "module m;\n"
      "  logic clk = 0;\n"
      "  int hits = 0;\n"
      "  leaf u();\n"
      "  assert property (@(posedge clk) u.req) hits = hits + 1;\n"
      "  initial begin\n"
      "    #5 u.req = 1;\n"
      "    #5 clk = 1;\n"
      "  end\n"
      "endmodule\n",
      f, "hits");
  ASSERT_NE(var, nullptr);
  EXPECT_EQ(var->value.ToUint64(), 1u);
}

TEST(ConcurrentAssertionSampling, LikeNamedOperandsAreSampledPerInstance) {
  SimFixture f;
  auto* var = RunAndFindVar(
      "module leaf;\n"
      "  logic req = 0;\n"
      "endmodule\n"
      "module m;\n"
      "  logic clk = 0;\n"
      "  int hits = 0;\n"
      "  leaf u1();\n"
      "  leaf u2();\n"
      "  assert property (@(posedge clk) u1.req && !u2.req) hits = hits + 1;\n"
      "  initial begin\n"
      "    #5 u1.req = 1;\n"
      "    #5 u2.req = 1;\n"
      "    clk = 1;\n"
      "  end\n"
      "endmodule\n",
      f, "hits");
  ASSERT_NE(var, nullptr);
  EXPECT_EQ(var->value.ToUint64(), 1u);
}

TEST(ConcurrentAssertionSampling, ConstCastReadsTheCurrentValueAtTheTick) {
  SimFixture f;
  auto* hits = RunAndFindVar(
      "module m;\n"
      "  logic clk;\n"
      "  logic a;\n"
      "  int hits = 0;\n"
      "  int misses = 0;\n"
      "  assert property (@(posedge clk) const'(a) != a) hits = hits + 1;\n"
      "  else misses = misses + 1;\n"
      "  initial begin\n"
      "    clk = 1'b0; a = 1'b0;\n"
      "    #5 a = 1'b1; clk = 1'b1;\n"
      "  end\n"
      "endmodule\n",
      f, "hits");
  ASSERT_NE(hits, nullptr);
  auto* misses = f.ctx.FindVariable("misses");
  ASSERT_NE(misses, nullptr);
  EXPECT_EQ(hits->value.ToUint64(), 1u);
  EXPECT_EQ(misses->value.ToUint64(), 0u);
}

TEST(ConcurrentAssertionSampling, AnArrayElementReadsItsPreponedValue) {
  SimFixture f;
  auto* pass = RunAndFindVar(
      "module m;\n"
      "  logic clk = 0;\n"
      "  logic arr [2:5] = '{1, 1, 1, 1};\n"
      "  int pass = 0, fail = 0;\n"
      "  always #5 clk = ~clk;\n"
      "  always @(posedge clk) arr[3] = ~arr[3];\n"
      "  a1: assert property (@(posedge clk) arr[3]) pass++; else fail++;\n"
      "  initial #52 $finish;\n"
      "endmodule\n",
      f, "pass");
  ASSERT_NE(pass, nullptr);
  EXPECT_EQ(pass->value.ToUint64(), 3u);
  EXPECT_EQ(f.ctx.FindVariable("fail")->value.ToUint64(), 2u);
}

TEST(ConcurrentAssertionSampling,
     AMultidimensionalElementReadsItsPreponedValue) {
  SimFixture f;
  auto* pass = RunAndFindVar(
      "module m;\n"
      "  logic clk = 0;\n"
      "  logic arr [1:0][1:0] = '{'{1, 1}, '{1, 1}};\n"
      "  int pass = 0, fail = 0;\n"
      "  always #5 clk = ~clk;\n"
      "  always @(posedge clk) arr[1][0] = ~arr[1][0];\n"
      "  a1: assert property (@(posedge clk) arr[1][0]) pass++; else fail++;\n"
      "  initial #52 $finish;\n"
      "endmodule\n",
      f, "pass");
  ASSERT_NE(pass, nullptr);
  EXPECT_EQ(pass->value.ToUint64(), 3u);
  EXPECT_EQ(f.ctx.FindVariable("fail")->value.ToUint64(), 2u);
}

TEST(ConcurrentAssertionSampling, APastTriggeredIsItsPostponedValue) {
  SimFixture f;
  auto* hits = RunAndFindVar(
      "module m;\n"
      "  logic clk = 0;\n"
      "  event e;\n"
      "  int hits = 0;\n"
      "  always #5 clk = ~clk;\n"
      "  a0: assert property (@(posedge clk) 1) -> e;\n"
      "  c1: cover property (@(posedge clk) $past(e.triggered)) hits++;\n"
      "  initial #42 $finish;\n"
      "endmodule\n",
      f, "hits");
  ASSERT_NE(hits, nullptr);
  EXPECT_EQ(hits->value.ToUint64(), 3u);
}

}  // namespace
