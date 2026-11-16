#include <gtest/gtest.h>

#include <string>
#include <vector>

#include "common/types.h"
#include "fixture_simulator.h"
#include "simulator/checker_instance_scheduling.h"
#include "simulator/checker_variable_randomization.h"

using namespace delta;

namespace {

TEST(CheckerVariableRandomization, CheckerAssumeIsCheckedForViolation) {
  EXPECT_TRUE(CheckerAssumeStatementIsCheckedForViolationDuringSimulation());
}

TEST(CheckerVariableRandomization, SolveTriggeredByAssumeSetClockEvent) {
  EXPECT_TRUE(AssumeRandomizationIsTriggeredBy(
      RandomizationTrigger::kAssumeSetClockEvent));
  EXPECT_FALSE(AssumeRandomizationIsTriggeredBy(
      RandomizationTrigger::kExplicitProceduralCall));
}

TEST(CheckerVariableRandomization, CheckersHaveNoRandomizeMethod) {
  EXPECT_FALSE(CheckersProvideRandomizeMethod());
}

TEST(CheckerVariableRandomization, HoldEndsAtWhicheverComesFirst) {
  EXPECT_EQ(FreeCheckerVariableHoldEndsAt(true),
            AssumeRandomizationHoldBoundary::kNextAssumeSetClockEvent);
  EXPECT_EQ(FreeCheckerVariableHoldEndsAt(false),
            AssumeRandomizationHoldBoundary::kEndOfTimeStep);
}

TEST(CheckerVariableRandomization, ActiveClassification) {
  EXPECT_TRUE(IsActiveForAssumeRandomization(
      AssumeRandomizationVariable::kFreeNonConstUnassigned));
  EXPECT_FALSE(IsActiveForAssumeRandomization(
      AssumeRandomizationVariable::kFreeNonConstAssigned));
  EXPECT_FALSE(IsActiveForAssumeRandomization(
      AssumeRandomizationVariable::kNonFreeCheckerVariable));
  EXPECT_FALSE(IsActiveForAssumeRandomization(
      AssumeRandomizationVariable::kCheckerFormal));
}

TEST(CheckerVariableRandomization, NoActivenessControlFacility) {
  EXPECT_FALSE(AssumeRandomizationProvidesActivenessControlFacility());
}

TEST(CheckerVariableRandomization, ElementActivenessGranularity) {
  EXPECT_FALSE(AssumeRandomizationElementsAreSeparatelyActive(
      CheckerVariableAggregate::kPackedArrayOrStruct));
  EXPECT_TRUE(AssumeRandomizationElementsAreSeparatelyActive(
      CheckerVariableAggregate::kUnpackedArrayOrStruct));
}

TEST(CheckerVariableRandomization, RandomInitialValueUnlessDeclared) {
  EXPECT_TRUE(FreeCheckerVariableTakesRandomInitialValue(false));
  EXPECT_FALSE(FreeCheckerVariableTakesRandomInitialValue(true));
}

TEST(CheckerVariableRandomization, OneAssumeSetPerInstanceMaybeEmpty) {
  EXPECT_EQ(AssumeSetsPerCheckerInstance(), 1);
  EXPECT_TRUE(AssumeSetMayBeEmpty());
}

TEST(CheckerVariableRandomization, AssumeSetExistsForStaticAndProcedural) {
  EXPECT_TRUE(AssumeSetExistsAtEveryTimeStep(CheckerInstanceKind::kStatic));
  EXPECT_TRUE(AssumeSetExistsAtEveryTimeStep(CheckerInstanceKind::kProcedural));
}

TEST(CheckerVariableRandomization, AssumeSetOriginContribution) {
  EXPECT_TRUE(AssumeStatementOriginContributesToAssumeSet(
      AssumeStatementOrigin::kOwnChecker));
  EXPECT_TRUE(AssumeStatementOriginContributesToAssumeSet(
      AssumeStatementOrigin::kChildChecker));
  EXPECT_FALSE(AssumeStatementOriginContributesToAssumeSet(
      AssumeStatementOrigin::kUnrelated));
}

TEST(CheckerVariableRandomization, AssumeSetMembership) {
  EXPECT_FALSE(AssumeStatementIsInAssumeSet({true, true}));
  EXPECT_FALSE(AssumeStatementIsInAssumeSet({true, false}));
  EXPECT_TRUE(AssumeStatementIsInAssumeSet({false, true}));
  EXPECT_FALSE(AssumeStatementIsInAssumeSet({false, false}));
}

TEST(CheckerVariableRandomization, SolutionAttemptOutcome) {
  EXPECT_EQ(AssumeSetSolutionAttempt(true),
            SolutionAttemptOutcome::kSuccessful);
  EXPECT_EQ(AssumeSetSolutionAttempt(false),
            SolutionAttemptOutcome::kUnsuccessful);
}

TEST(CheckerVariableRandomization, NoSolutionGuarantees) {
  EXPECT_FALSE(AssumeRandomizationMustFindSolutionWhenItExists());
  EXPECT_FALSE(AssumeRandomizationMustAvoidDeadEndStates());
}

TEST(CheckerVariableRandomization, EmptyAssumeSetImplicitClock) {
  EXPECT_TRUE(EmptyAssumeSetHasImplicitClockEvent());
  EXPECT_EQ(EmptyAssumeSetImplicitClockEventRegion(), Region::kPreObserved);
  EXPECT_LT(static_cast<int>(EmptyAssumeSetImplicitClockEventRegion()),
            static_cast<int>(Region::kObserved));
}

TEST(CheckerVariableRandomization, ActiveVariableClocking) {
  EXPECT_EQ(ActiveVariableClocking(true),
            AssumeSetClocking::kImplicitlyClocked);
  EXPECT_EQ(ActiveVariableClocking(false),
            AssumeSetClocking::kExplicitlyClocked);
}

TEST(CheckerVariableRandomization, ImplicitlyClockedUpdateAndHold) {
  EXPECT_TRUE(ImplicitlyClockedVariableUpdatesEveryTimeStep());
  EXPECT_TRUE(ImplicitlyClockedVariableStaysConstantUntilEndOfTimeStep());
}

TEST(CheckerVariableRandomization,
     AbsentActiveVariableUnconstrainedButClocked) {
  EXPECT_EQ(ActiveVariableAbsentFromNonemptyAssumeSetClocking(),
            AssumeSetClocking::kExplicitlyClocked);
  EXPECT_FALSE(ActiveVariableAbsentFromNonemptyAssumeSetIsConstrained());
}

TEST(CheckerVariableRandomization, SolveAtObservedWithCurrentValues) {
  EXPECT_EQ(AssumeRandomizationSolvePrecedesRegion(), Region::kObserved);
  EXPECT_TRUE(SampledValueOfActiveCheckerVariableIsCurrentValue());
}

TEST(CheckerVariableRandomization, UnsuccessfulFailureSurfacesInObserved) {
  EXPECT_EQ(AssumptionFailureRegionAfterUnsuccessfulSolve(), Region::kObserved);
}

TEST(CheckerVariableRandomization, FreeVariableSatisfiesItsAssumptions) {
  SimFixture f;
  auto* pass = RunAndFindVar(
      "checker chk(logic clk);\n"
      "  rand bit r;\n"
      "  int pass = 0, fail = 0;\n"
      "  m1: assume property (@(posedge clk) r == 1'b1);\n"
      "  a1: assert property (@(posedge clk) r) pass++; else fail++;\n"
      "endchecker\n"
      "checker c2(logic bclk, logic x);\n"
      "  rand bit m;\n"
      "  u1: assume property (@(posedge bclk) m == x);\n"
      "  int pass = 0, fail = 0;\n"
      "  a1: assert property (@(posedge bclk) m == x) pass++; else fail++;\n"
      "endchecker\n"
      "checker c1(logic fclk, logic a);\n"
      "  c2 B1(fclk, a);\n"
      "endchecker\n"
      "module top;\n"
      "  logic clk = 0, a = 1;\n"
      "  always #5 clk = ~clk;\n"
      "  chk c(clk);\n"
      "  c1 F1(clk, a);\n"
      "  initial begin #12 a = 0; #20 a = 1; #20 $finish; end\n"
      "endmodule\n",
      f, "c.pass");
  ASSERT_NE(pass, nullptr);
  EXPECT_EQ(pass->value.ToUint64(), 5u);
  EXPECT_EQ(f.ctx.FindVariable("c.fail")->value.ToUint64(), 0u);
  EXPECT_EQ(f.ctx.FindVariable("F1.B1.pass")->value.ToUint64(), 5u);
  EXPECT_EQ(f.ctx.FindVariable("F1.B1.fail")->value.ToUint64(), 0u);
}

TEST(CheckerVariableRandomization, AConstantFreeVariableKeepsItsRandomValue) {
  SimFixture f;
  auto* k = RunAndFindVar(
      "checker chk(logic clk);\n"
      "  rand const bit [31:0] k;\n"
      "  rand const bit [7:0] k7 = 8'd7;\n"
      "  rand bit [31:0] r;\n"
      "  m1: assume property (@(posedge clk) r != k);\n"
      "  bit [31:0] last;\n"
      "  bit seen = 1'b0;\n"
      "  int changed = 0;\n"
      "  always_ff @(posedge clk) begin\n"
      "    if (seen && k != last) changed <= changed + 1;\n"
      "    last <= k;\n"
      "    seen <= 1'b1;\n"
      "  end\n"
      "endchecker\n"
      "module top;\n"
      "  logic clk = 0;\n"
      "  always #5 clk = ~clk;\n"
      "  chk c(clk);\n"
      "  initial #60 $finish;\n"
      "endmodule\n",
      f, "c.k");
  ASSERT_NE(k, nullptr);
  EXPECT_NE(k->value.ToUint64(), 0u);
  EXPECT_EQ(f.ctx.FindVariable("c.k7")->value.ToUint64(), 7u);
  EXPECT_EQ(f.ctx.FindVariable("c.last")->value.ToUint64(),
            k->value.ToUint64());
  EXPECT_EQ(f.ctx.FindVariable("c.changed")->value.ToUint64(), 0u);
  EXPECT_NE(f.ctx.FindVariable("c.r")->value.ToUint64(), k->value.ToUint64());
}

TEST(CheckerVariableRandomization, AnAssignedFreeVariableIsNotSolvedFor) {
  SimFixture f;
  auto* pass = RunAndFindVar(
      "checker chk(logic clk);\n"
      "  rand bit a = 1'b0;\n"
      "  rand bit b;\n"
      "  bit [3:0] cnt = 4'd0;\n"
      "  int pass = 0, fail = 0, bpass = 0;\n"
      "  m1: assume property (@(posedge clk) b == 1'b1);\n"
      "  always_ff @(posedge clk) a <= !a;\n"
      "  always_ff @(posedge clk) cnt <= cnt + 4'd1;\n"
      "  a1: assert property (@(posedge clk) a == cnt[0]) pass++; else "
      "fail++;\n"
      "  a2: assert property (@(posedge clk) b) bpass++;\n"
      "endchecker\n"
      "module top;\n"
      "  logic clk = 0;\n"
      "  always #5 clk = ~clk;\n"
      "  chk c(clk);\n"
      "  initial #100 $finish;\n"
      "endmodule\n",
      f, "c.pass");
  ASSERT_NE(pass, nullptr);
  EXPECT_EQ(pass->value.ToUint64(), 10u);
  EXPECT_EQ(f.ctx.FindVariable("c.fail")->value.ToUint64(), 0u);
  EXPECT_EQ(f.ctx.FindVariable("c.bpass")->value.ToUint64(), 10u);
}

TEST(CheckerVariableRandomization, AnEmptyAssumeSetDrawsAtEveryTimeStep) {
  SimFixture f;
  auto* changes = RunAndFindVar(
      "checker chk(logic clk);\n"
      "  rand bit [7:0] r;\n"
      "  m1: assume property (@(posedge clk) clk);\n"
      "  int changes = 0;\n"
      "  bit [7:0] last;\n"
      "  always_ff @(posedge clk) begin\n"
      "    if (r != last) changes <= changes + 1;\n"
      "    last <= r;\n"
      "  end\n"
      "endchecker\n"
      "module top;\n"
      "  logic clk = 0;\n"
      "  always #5 clk = ~clk;\n"
      "  chk c(clk);\n"
      "  initial #200 $finish;\n"
      "endmodule\n",
      f, "c.changes");
  ASSERT_NE(changes, nullptr);
  EXPECT_GT(changes->value.ToUint64(), 10u);
}

TEST(CheckerVariableRandomization, EachAssumptionsClockTriggersAnAttempt) {
  SimFixture f;
  auto* bad1 = RunAndFindVar(
      "checker chk(logic clk1, logic clk2);\n"
      "  rand bit v;\n"
      "  m1: assume property (@(posedge clk1) v == 1'b1);\n"
      "  m2: assume property (@(posedge clk2) v == 1'b0);\n"
      "  m3: assume property (@(posedge clk1) v || !v);\n"
      "  int bad1 = 0, bad2 = 0, good1 = 0, good2 = 0;\n"
      "  always_ff @(posedge clk1)\n"
      "    if (v != 1'b1) bad1 <= bad1 + 1; else good1 <= good1 + 1;\n"
      "  always_ff @(posedge clk2)\n"
      "    if (v != 1'b0) bad2 <= bad2 + 1; else good2 <= good2 + 1;\n"
      "endchecker\n"
      "module top;\n"
      "  logic clk1 = 0, clk2 = 0;\n"
      "  always #5 clk1 = ~clk1;\n"
      "  initial begin #2; forever #5 clk2 = ~clk2; end\n"
      "  chk c(clk1, clk2);\n"
      "  initial #100 $finish;\n"
      "endmodule\n",
      f, "c.bad1");
  ASSERT_NE(bad1, nullptr);
  EXPECT_EQ(bad1->value.ToUint64(), 0u);
  EXPECT_EQ(f.ctx.FindVariable("c.bad2")->value.ToUint64(), 0u);
  EXPECT_EQ(f.ctx.FindVariable("c.good1")->value.ToUint64(), 10u);
  EXPECT_EQ(f.ctx.FindVariable("c.good2")->value.ToUint64(), 10u);
}

TEST(CheckerVariableRandomization, AnImplicationConstrainsItsTimeStep) {
  SimFixture f;
  auto* fail1 = RunAndFindVar(
      "checker chk(logic clk);\n"
      "  rand bit x, y;\n"
      "  int fail1 = 0, fail2 = 0, ones = 0;\n"
      "  m1: assume property (@(posedge clk) x |=> !x);\n"
      "  m2: assume property (@(posedge clk) x |-> y);\n"
      "  m3: assume property (@(posedge clk) x |-> ##1 1'b1);\n"
      "  m4: assume property (@(posedge clk) x ##1 1'b1 |-> 1'b1);\n"
      "  m5: assume property (@(posedge clk) ##1 x |-> 1'b1);\n"
      "  m6: assume property (@(posedge clk) x or 1'b1);\n"
      "  m7: assume property (@(posedge clk) 1'b1 ##1 1'b1);\n"
      "  m8: assume property (@(posedge clk) not (x && !x));\n"
      "  a1: assert property (@(posedge clk) x |=> !x) else fail1++;\n"
      "  a2: assert property (@(posedge clk) x |-> y) else fail2++;\n"
      "  a3: assert property (@(posedge clk) !x) else ones++;\n"
      "endchecker\n"
      "module top;\n"
      "  logic clk = 0;\n"
      "  always #5 clk = ~clk;\n"
      "  chk c(clk);\n"
      "  initial #400 $finish;\n"
      "endmodule\n",
      f, "c.fail1");
  ASSERT_NE(fail1, nullptr);
  EXPECT_EQ(fail1->value.ToUint64(), 0u);
  EXPECT_EQ(f.ctx.FindVariable("c.fail2")->value.ToUint64(), 0u);
  EXPECT_GT(f.ctx.FindVariable("c.ones")->value.ToUint64(), 0u);
}

TEST(CheckerVariableRandomization, AChildsAssumptionConstrainsItsParent) {
  SimFixture f;
  auto* fail = RunAndFindVar(
      "checker child(logic clk, bit [7:0] x);\n"
      "  u1: assume property (@(posedge clk) x == 8'd42);\n"
      "endchecker\n"
      "checker parent(logic clk);\n"
      "  rand bit [7:0] q;\n"
      "  child B1(clk, q);\n"
      "  int pass = 0, fail = 0;\n"
      "  a1: assert property (@(posedge clk) q == 8'd42) pass++; else fail++;\n"
      "endchecker\n"
      "module top;\n"
      "  logic clk = 0;\n"
      "  always #5 clk = ~clk;\n"
      "  parent p(clk);\n"
      "  initial #60 $finish;\n"
      "endmodule\n",
      f, "p.fail");
  ASSERT_NE(fail, nullptr);
  EXPECT_EQ(fail->value.ToUint64(), 0u);
  EXPECT_EQ(f.ctx.FindVariable("p.pass")->value.ToUint64(), 6u);
}

TEST(CheckerVariableRandomization, AConstCastOrAutomaticActualIsExcluded) {
  SimFixture f;
  auto* q1 = RunAndFindVar(
      "checker c(logic clk, bit [7:0] a, bit [7:0] b);\n"
      "  rand bit [7:0] q;\n"
      "  u3: assume property (@(posedge clk) q == a);\n"
      "  u4: assume property (@(posedge clk) q != b);\n"
      "endchecker\n"
      "module top;\n"
      "  logic clk = 0;\n"
      "  logic [7:0] v1 = 8'd5, v2 = 8'd5;\n"
      "  always #5 clk = ~clk;\n"
      "  c F1(clk, v1, const'(v2));\n"
      "  always @(posedge clk) begin\n"
      "    automatic bit [7:0] w = 8'd5;\n"
      "    c F2(clk, v1, w);\n"
      "  end\n"
      "  c F3(clk, v1, 8'(v2));\n"
      "  initial #30 $finish;\n"
      "endmodule\n",
      f, "F1.q");
  ASSERT_NE(q1, nullptr);
  EXPECT_EQ(q1->value.ToUint64(), 5u);
  EXPECT_EQ(f.ctx.FindVariable("F2.q")->value.ToUint64(), 5u);
  EXPECT_NE(f.ctx.FindVariable("F3.q")->value.ToUint64(), 5u);
}

std::string AssumedPropertySource(const std::string& property,
                                  const std::string& decls,
                                  const std::string& unit) {
  return unit +
         "checker chk(logic clk);\n"
         "  rand bit x, y, z;\n" +
         decls +
         "  int fail = 0, ones = 0;\n"
         "  m1: assume property (@(posedge clk) " +
         property +
         ");\n"
         "  a1: assert property (@(posedge clk) " +
         property +
         ") else if ($time < 400) fail++;\n"
         "  always_ff @(posedge clk) if (x) ones <= ones + 1;\n"
         "endchecker\n"
         "module top;\n"
         "  logic clk = 0;\n"
         "  always #5 clk = ~clk;\n"
         "  chk c(clk);\n"
         "  initial #400 $finish;\n"
         "endmodule\n";
}

void ExpectAssumedPropertiesHold(const std::vector<std::string>& properties,
                                 const std::string& decls = "",
                                 const std::string& unit = "") {
  for (const std::string& property : properties) {
    SCOPED_TRACE(property);
    SimFixture f;
    auto* fail = RunAndFindVar(AssumedPropertySource(property, decls, unit), f,
                               "c.fail");
    ASSERT_NE(fail, nullptr);
    EXPECT_EQ(fail->value.ToUint64(), 0u);
    EXPECT_GT(f.ctx.FindVariable("c.ones")->value.ToUint64(), 0u);
  }
}

TEST(CheckerVariableRandomization, AFixedDelaySequenceConstrainsLaterTicks) {
  ExpectAssumedPropertiesHold({"x |-> ##1 y", "x ##1 y |-> z", "x |=> ##2 y",
                               "x ##0 y |-> ##1 z", "##1 x |-> y", "x ##1 y"});
}

TEST(CheckerVariableRandomization, AnOperatorAtOneTickConstrainsItsTick) {
  ExpectAssumedPropertiesHold(
      {"if (x) y else z", "if (x) y", "x implies y", "x iff y", "not (x && y)",
       "not (x ##1 y)", "not (x |=> y)", "not (##1 x |-> y)",
       "x |-> not nexttime y", "x or nexttime y", "(x and nexttime y) or z",
       "case (x) 1'b1: y; default: z; endcase"});
}

TEST(CheckerVariableRandomization, ATemporalOperatorConstrainsLaterTicks) {
  ExpectAssumedPropertiesHold({"nexttime x", "x |-> nexttime [2] y",
                               "always [1:2] x", "always (x and nexttime y)",
                               "x |-> eventually [0:1] y", "x until y",
                               "x until_with y", "accept_on (z) x |-> ##1 y",
                               "reject_on (z) x |-> ##1 y"});
}

void ExpectXDrawnFree(const std::string& assumptions) {
  SimFixture f;
  auto* ones = RunAndFindVar(
      "checker chk(logic clk);\n"
      "  rand bit x, y, z;\n"
      "  int ones = 0, zeros = 0;\n" +
          assumptions +
          "  always_ff @(posedge clk)\n"
          "    if (x) ones <= ones + 1; else zeros <= zeros + 1;\n"
          "endchecker\n"
          "module top;\n"
          "  logic clk = 0;\n"
          "  always #5 clk = ~clk;\n"
          "  chk c(clk);\n"
          "  initial #400 $finish;\n"
          "endmodule\n",
      f, "c.ones");
  ASSERT_NE(ones, nullptr);
  EXPECT_GT(ones->value.ToUint64(), 0u);
  EXPECT_GT(f.ctx.FindVariable("c.zeros")->value.ToUint64(), 0u);
}

TEST(CheckerVariableRandomization, AnEventualityLeavesItsTickFree) {
  ExpectXDrawnFree("  m1: assume property (@(posedge clk) s_eventually x);\n");
}

TEST(CheckerVariableRandomization, AVaryingSequenceConstrainsLaterTicks) {
  ExpectAssumedPropertiesHold({"x |-> ##[1:2] y", "x |-> ##[1:$] y",
                               "x |-> y[*2]", "x |-> y[*1:$] ##1 z",
                               "x |-> y[->1] ##1 z", "x |-> y[=1] ##1 z",
                               "x |-> y[->2:3] ##1 z", "x ##[0:1] y |-> z"});
}

TEST(CheckerVariableRandomization, ADisabledAssumptionHoldsNoAttempt) {
  SimFixture f;
  auto* zeros = RunAndFindVar(
      "checker chk(logic clk, logic rst);\n"
      "  rand bit x;\n"
      "  int zeros = 0, fail = 0;\n"
      "  m1: assume property (@(posedge clk) disable iff (rst) x);\n"
      "  a1: assert property (@(posedge clk) disable iff (rst) x) else "
      "fail++;\n"
      "  always_ff @(posedge clk) if (rst && !x) zeros <= zeros + 1;\n"
      "endchecker\n"
      "module top;\n"
      "  logic clk = 0, rst = 1;\n"
      "  always #5 clk = ~clk;\n"
      "  chk c(clk, rst);\n"
      "  initial begin #200 rst = 0; #200 $finish; end\n"
      "endmodule\n",
      f, "c.zeros");
  ASSERT_NE(zeros, nullptr);
  EXPECT_GT(zeros->value.ToUint64(), 0u);
  EXPECT_EQ(f.ctx.FindVariable("c.fail")->value.ToUint64(), 0u);
}

TEST(CheckerVariableRandomization, AnEmptyMatchConstrainsItsNeighbours) {
  ExpectAssumedPropertiesHold({"x |-> y[*0:1] ##1 z", "x |-> z ##[1:2] y[*0:1]",
                               "x ##1 y[*0:1] ##1 z"});
}

TEST(CheckerVariableRandomization, ASequenceOperatorConstrainsLaterTicks) {
  ExpectAssumedPropertiesHold(
      {"(x ##1 y or y ##1 x) |-> z", "(x ##1 y and y) |-> z",
       "(x ##[1:2] y intersect z ##1 1'b1) |-> y",
       "first_match(x ##[1:2] y) |-> z", "z throughout (x ##1 y) |-> ##1 y",
       "(x ##1 y) within (z ##3 z) |-> y", "x |-> (y ##1 z)[*2]",
       "x |-> (y or z ##1 y)[*1:2] ##1 z", "x ##1 (z throughout y ##1 y)",
       "(x ##1 (z throughout y)) |-> z"});
}

TEST(CheckerVariableRandomization, ALocalVariableCarriesItsValue) {
  ExpectAssumedPropertiesHold(
      {"s1", "s2", "s3", "s4", "s5", "x ##1 s4", "s6", "s7", "s8"},
      "  sequence s1; bit v; (1, v = x) ##1 (y == v); endsequence\n"
      "  sequence s3; bit v; bit w; (1, v = x, w = y) ##1 (z == (v ^ w));\n"
      "  endsequence\n"
      "  sequence s4; bit v; ((1, v = x) ##1 y == v) or (z ##1 y == z);\n"
      "  endsequence\n"
      "  sequence s5; bit v; ((1, v = x) ##1 y == v) and (z ##2 1'b1);\n"
      "  endsequence\n"
      "  sequence s6; bit v; (y, v = x)[*2] ##1 x != v; endsequence\n"
      "  sequence s7; bit v; (y[->2], v = x) ##1 x != v; endsequence\n"
      "  sequence s8; bit v; (y[=1], v = x) ##1 x != v; endsequence\n"

      "  sequence s2; bit [1:0] v; (1, v = x) ##1 (1, v += x) ##1 "
      "(y == (v == 2'd1)); endsequence\n");
}

TEST(CheckerVariableRandomization, ALocalsSelectCarriesItsValue) {
  ExpectAssumedPropertiesHold(
      {"s1", "s2"},
      "  sequence s1; bit [1:0] v; (1, v = 0, v[1] = x) ##1 "
      "(y == v[1] && !v[0]); endsequence\n"
      "  sequence s2; bit [1:0] v; (1, v = 2'b01, v[1] += x) ##1 "
      "(y == v[1] && v[0]); endsequence\n");
}

TEST(CheckerVariableRandomization,
     ALocalsMemberOrSelectResolvesAgainstItsType) {
  ExpectAssumedPropertiesHold(
      {"s1", "s2"},
      "  sequence s1; pair_t p = 8'h3C; (1, p.lo = x) ##1 "
      "(y == p.lo && p.hi == 3); endsequence\n"
      "  sequence s2; logic [8:1] v = 1; (1, v[2] = x) ##1 "
      "(y == v[2] && v[1]); endsequence\n",
      "typedef struct packed { logic [3:0] hi, lo; } pair_t;\n");
}

TEST(CheckerVariableRandomization, AnOperandOnItsOwnClockConstrainsItsTicks) {
  ExpectAssumedPropertiesHold(
      {"x |=> @(negedge clk) y", "x ##1 @(negedge clk) y |-> z",
       "x |-> @(negedge clk) (if (y) z else !z)",
       "x |-> @(negedge clk) nexttime y",
       "x |-> @(negedge clk) accept_on (z) y", "x |-> @(negedge clk) y[*2]",
       "x |-> @(negedge clk) y[->1] ##1 z",
       "x |-> @(negedge clk) (z throughout y ##1 y)"},
      "  m2: assume property (@(posedge clk) !y);\n");
}

TEST(CheckerVariableRandomization, APropertyInstanceConstrainsItsBody) {
  ExpectAssumedPropertiesHold(
      {"p1(x, y)", "p1(.a(x), .b(y))", "p2", "p3", "p4"},
      "  property p1(a, b); a |-> ##1 b; endproperty\n"
      "  property p2; x and nexttime p2; endproperty\n"
      "  property p3; @(posedge clk) x |-> z; endproperty\n"
      "  property p4; bit v; (1, v = y) |=> x == v; endproperty\n");
}

}  // namespace
