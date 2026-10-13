#include <gtest/gtest.h>

#include <string>
#include <vector>

#include "common/types.h"
#include "fixture_simulator.h"
#include "simulator/checker_instance_scheduling.h"
#include "simulator/checker_variable_randomization.h"

using namespace delta;

namespace {

// §17.7.2: like ordinary assume statements, a checker assume statement is also
// checked for violation during simulation.
TEST(CheckerVariableRandomization, CheckerAssumeIsCheckedForViolation) {
  EXPECT_TRUE(CheckerAssumeStatementIsCheckedForViolationDuringSimulation());
}

// §17.7.2: solving is triggered by an assume set clock event, not by an
// explicit procedural call such as randomize().
TEST(CheckerVariableRandomization, SolveTriggeredByAssumeSetClockEvent) {
  EXPECT_TRUE(AssumeRandomizationIsTriggeredBy(
      RandomizationTrigger::kAssumeSetClockEvent));
  EXPECT_FALSE(AssumeRandomizationIsTriggeredBy(
      RandomizationTrigger::kExplicitProceduralCall));
}

// §17.7.2: there is no randomize() for checkers.
TEST(CheckerVariableRandomization, CheckersHaveNoRandomizeMethod) {
  EXPECT_FALSE(CheckersProvideRandomizeMethod());
}

// §17.7.2: an updated free checker variable holds its value until the next
// assume set clock event or the end of the time step, whichever comes first.
TEST(CheckerVariableRandomization, HoldEndsAtWhicheverComesFirst) {
  EXPECT_EQ(FreeCheckerVariableHoldEndsAt(
                /*next_clock_event_before_end_of_time_step=*/true),
            AssumeRandomizationHoldBoundary::kNextAssumeSetClockEvent);
  EXPECT_EQ(FreeCheckerVariableHoldEndsAt(
                /*next_clock_event_before_end_of_time_step=*/false),
            AssumeRandomizationHoldBoundary::kEndOfTimeStep);
}

// §17.7.2: a non-const free checker variable is active unless it appears on the
// left-hand side of a checker variable assignment, in which case it is
// inactive; non-free checker variables and checker formals are always inactive.
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

// §17.7.2: activeness mirrors rand variables but without an explicit control
// facility such as rand_mode().
TEST(CheckerVariableRandomization, NoActivenessControlFacility) {
  EXPECT_FALSE(AssumeRandomizationProvidesActivenessControlFacility());
}

// §17.7.2: a packed array or structure is active or inactive monolithically,
// whereas the elements of an unpacked array or structure are separately active.
TEST(CheckerVariableRandomization, ElementActivenessGranularity) {
  EXPECT_FALSE(AssumeRandomizationElementsAreSeparatelyActive(
      CheckerVariableAggregate::kPackedArrayOrStruct));
  EXPECT_TRUE(AssumeRandomizationElementsAreSeparatelyActive(
      CheckerVariableAggregate::kUnpackedArrayOrStruct));
}

// §17.7.2: every free checker variable is initialized with an unconstrained
// random value unless explicitly initialized in its declaration.
TEST(CheckerVariableRandomization, RandomInitialValueUnlessDeclared) {
  EXPECT_TRUE(FreeCheckerVariableTakesRandomInitialValue(
      /*has_declaration_initializer=*/false));
  EXPECT_FALSE(FreeCheckerVariableTakesRandomInitialValue(
      /*has_declaration_initializer=*/true));
}

// §17.7.2: each checker instance has one and only one assume set, which may be
// empty.
TEST(CheckerVariableRandomization, OneAssumeSetPerInstanceMaybeEmpty) {
  EXPECT_EQ(AssumeSetsPerCheckerInstance(), 1);
  EXPECT_TRUE(AssumeSetMayBeEmpty());
}

// §17.7.2: checker assume sets exist at every time step regardless of whether
// the checker instance is static or procedural.
TEST(CheckerVariableRandomization, AssumeSetExistsForStaticAndProcedural) {
  EXPECT_TRUE(AssumeSetExistsAtEveryTimeStep(CheckerInstanceKind::kStatic));
  EXPECT_TRUE(AssumeSetExistsAtEveryTimeStep(CheckerInstanceKind::kProcedural));
}

// §17.7.2: an assume set is formed from the checker's own assume statements and
// those of its child checkers; unrelated statements do not contribute.
TEST(CheckerVariableRandomization, AssumeSetOriginContribution) {
  EXPECT_TRUE(AssumeStatementOriginContributesToAssumeSet(
      AssumeStatementOrigin::kOwnChecker));
  EXPECT_TRUE(AssumeStatementOriginContributesToAssumeSet(
      AssumeStatementOrigin::kChildChecker));
  EXPECT_FALSE(AssumeStatementOriginContributesToAssumeSet(
      AssumeStatementOrigin::kUnrelated));
}

// §17.7.2: a candidate statement that references a const-cast or
// automatic-value actual is excluded; of the rest, only those referencing an
// active free variable are included.
TEST(CheckerVariableRandomization, AssumeSetMembership) {
  // Excluded because of the const-cast / automatic actual, even though it would
  // otherwise reference an active free variable.
  EXPECT_FALSE(AssumeStatementIsInAssumeSet(
      {/*const_cast_or_automatic=*/true, /*active_free_var=*/true}));
  // Excluded by the const-cast actual with no active free variable referenced
  // at all — the case of the clause's own F1.u4, whose only formal is bound to
  // a const-cast actual. Both exclusion reasons hold at once.
  EXPECT_FALSE(AssumeStatementIsInAssumeSet(
      {/*const_cast_or_automatic=*/true, /*active_free_var=*/false}));
  // Included: no excluded actual, and it references an active free variable.
  EXPECT_TRUE(AssumeStatementIsInAssumeSet(
      {/*const_cast_or_automatic=*/false, /*active_free_var=*/true}));
  // Not included: no excluded actual, but references no active free variable.
  EXPECT_FALSE(AssumeStatementIsInAssumeSet(
      {/*const_cast_or_automatic=*/false, /*active_free_var=*/false}));
}

// §17.7.2: a solution attempt is successful exactly when satisfying values are
// found for the active variables; otherwise it is unsuccessful.
TEST(CheckerVariableRandomization, SolutionAttemptOutcome) {
  EXPECT_EQ(AssumeSetSolutionAttempt(/*satisfying_values_found=*/true),
            SolutionAttemptOutcome::kSuccessful);
  EXPECT_EQ(AssumeSetSolutionAttempt(/*satisfying_values_found=*/false),
            SolutionAttemptOutcome::kUnsuccessful);
}

// §17.7.2: there is no requirement that a solution be found when one exists,
// nor that dead-end states be avoided.
TEST(CheckerVariableRandomization, NoSolutionGuarantees) {
  EXPECT_FALSE(AssumeRandomizationMustFindSolutionWhenItExists());
  EXPECT_FALSE(AssumeRandomizationMustAvoidDeadEndStates());
}

// §17.7.2: an empty assume set carries an implicit assume set clock event in
// every time step, placed before the Observed region.
TEST(CheckerVariableRandomization, EmptyAssumeSetImplicitClock) {
  EXPECT_TRUE(EmptyAssumeSetHasImplicitClockEvent());
  EXPECT_EQ(EmptyAssumeSetImplicitClockEventRegion(), Region::kPreObserved);
  // The implicit event precedes the Observed region in the region order.
  EXPECT_LT(static_cast<int>(EmptyAssumeSetImplicitClockEventRegion()),
            static_cast<int>(Region::kObserved));
}

// §17.7.2: active variables of a checker with an empty assume set are
// implicitly clocked; with a nonempty assume set they are explicitly clocked.
TEST(CheckerVariableRandomization, ActiveVariableClocking) {
  EXPECT_EQ(ActiveVariableClocking(/*assume_set_is_empty=*/true),
            AssumeSetClocking::kImplicitlyClocked);
  EXPECT_EQ(ActiveVariableClocking(/*assume_set_is_empty=*/false),
            AssumeSetClocking::kExplicitlyClocked);
}

// §17.7.2: an implicitly clocked active free variable may be updated at every
// time step and then stays constant until the end of the time step.
TEST(CheckerVariableRandomization, ImplicitlyClockedUpdateAndHold) {
  EXPECT_TRUE(ImplicitlyClockedVariableUpdatesEveryTimeStep());
  EXPECT_TRUE(ImplicitlyClockedVariableStaysConstantUntilEndOfTimeStep());
}

// §17.7.2: an active variable that appears in no property of a nonempty assume
// set is unconstrained but still explicitly clocked.
TEST(CheckerVariableRandomization,
     AbsentActiveVariableUnconstrainedButClocked) {
  EXPECT_EQ(ActiveVariableAbsentFromNonemptyAssumeSetClocking(),
            AssumeSetClocking::kExplicitlyClocked);
  EXPECT_FALSE(ActiveVariableAbsentFromNonemptyAssumeSetIsConstrained());
}

// §17.7.2: the active free checker variables are solved for as the
// implementation is about to begin the Observed region, using sampled values
// that, for an active checker variable, are its current value.
TEST(CheckerVariableRandomization, SolveAtObservedWithCurrentValues) {
  EXPECT_EQ(AssumeRandomizationSolvePrecedesRegion(), Region::kObserved);
  EXPECT_TRUE(SampledValueOfActiveCheckerVariableIsCurrentValue());
}

// §17.7.2: after an unsuccessful solution attempt, an assumption failure does
// not occur until the unsatisfied property is clocked and checked in the
// Observed region.
TEST(CheckerVariableRandomization, UnsuccessfulFailureSurfacesInObserved) {
  EXPECT_EQ(AssumptionFailureRegionAfterUnsuccessfulSolve(), Region::kObserved);
}

// §17.7.2: a free checker variable takes, at each clocking event of the
// assume set, a value satisfying the assumptions, so neither the assumption
// on it nor an assertion of the same condition fails at any of the five
// posedges, in a checker and in a checker instantiated inside another whose
// formal is the parent's. The free variable took no value from the
// assumptions, which failed at every posedge (and at three of B1's).
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

// §17.7 and §17.7.2: every free variable whose declaration writes no
// initializer starts at an unconstrained random value, a constant one
// among them, which keeps it: k is drawn once and never solved for, while
// r, the active variable, is solved to differ from it at every posedge.
// k7's initializer gives it its value.
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

// §17.7.2: a free variable a checker variable assignment writes is inactive
// and keeps the values the assignment gives it: a toggles at each posedge in
// step with cnt's low bit, while b, the one active variable, satisfies m1.
// Solved for as well, a would take a random value at each posedge.
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

// §17.7.2: with an empty assume set the active free variables take new
// unconstrained values at every time step: r, which no assumption reads,
// changes across the posedges, the assumption m1 reading clk alone.
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

// §17.7.2: every clock event of the assume set triggers a solution attempt
// held to the assumptions clocked there: v is solved to 1 at each posedge of
// clk1 and to 0 at each posedge of clk2, the two never coinciding. m3, on
// clk1 as well, ticks with m1 for one attempt between them.
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

// §17.7.2: an attempt seeks values with which no assumption of the set fails
// in its time step, an implication's among them: after a tick where x is 1,
// m1 requires x to be 0, and wherever x is 1, m2 requires y to be. The other
// assumptions hold under any values and so put no condition on it.
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

// §17.7.2: a child checker's assumptions belong to its parent's assume set
// where, through their actuals, they read the parent's active free
// variables: B1.u1 holds x, bound to q, at 1, so q is solved to 1.
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

// §17.7.2 with §17.3: an assumption reading a formal whose actual holds a
// const cast, as F1's b does, or an automatic value, as F2's b does, is left
// out of the assume set, so q is solved by u3 alone. F3's b, under a cast
// that is not const, keeps u4, which then contradicts u3.
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

// A checker whose free variables x, y and z the assumption m1 of `property`
// constrains, the declarations `decls` beside, the assertion a1 of the same
// property counting its failures before the run ends, where attempts still
// in flight are decided whatever the values, and `ones` the posedges at
// which x is 1, over 40 posedges of clk.
std::string AssumedPropertySource(const std::string& property,
                                  const std::string& decls) {
  return "checker chk(logic clk);\n"
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

// §17.7.2: under each of `properties` assumed, the declarations `decls`
// beside, no attempt of the property fails, while x is still 1 at some
// posedges, so that the obligations the property sets are met rather than
// never raised. Left out of the solution attempts, as a form they did not
// solve, each property failed.
void ExpectAssumedPropertiesHold(const std::vector<std::string>& properties,
                                 const std::string& decls = "") {
  for (const std::string& property : properties) {
    SCOPED_TRACE(property);
    SimFixture f;
    auto* fail =
        RunAndFindVar(AssumedPropertySource(property, decls), f, "c.fail");
    ASSERT_NE(fail, nullptr);
    EXPECT_EQ(fail->value.ToUint64(), 0u);
    EXPECT_GT(f.ctx.FindVariable("c.ones")->value.ToUint64(), 0u);
  }
}

// §17.7.2 with §16.7 and §16.12.7: an assumption over sequences of booleans
// under fixed delays holds each attempt still in flight to the operand it
// reads at the time step: a consequent's later operand, an antecedent of
// two operands, ##0 among them, a leading delay, a nonoverlapped
// implication and a sequence assumed alone.
TEST(CheckerVariableRandomization, AFixedDelaySequenceConstrainsLaterTicks) {
  ExpectAssumedPropertiesHold({"x |-> ##1 y", "x ##1 y |-> z", "x |=> ##2 y",
                               "x ##0 y |-> ##1 z", "##1 x |-> y", "x ##1 y"});
}

// §17.7.2 with §16.12.3 to §16.12.8 and §16.12.16: an assumption under the
// operators that join their operands at one tick holds the attempt to the
// condition they make of them: if-else with and without its else, implies,
// iff, a not over a boolean, a sequence, two implications and a nexttime,
// an or, an and, and a case with a default.
TEST(CheckerVariableRandomization, AnOperatorAtOneTickConstrainsItsTick) {
  ExpectAssumedPropertiesHold(
      {"if (x) y else z", "if (x) y", "x implies y", "x iff y", "not (x && y)",
       "not (x ##1 y)", "not (x |=> y)", "not (##1 x |-> y)",
       "x |-> not nexttime y", "x or nexttime y", "(x and nexttime y) or z",
       "case (x) 1'b1: y; default: z; endcase"});
}

// §17.7.2 with §16.12.10 to §16.12.14: an assumption under the operators
// that carry an obligation to later ticks holds the attempt to what each
// owes at the time step: nexttime with and without its count, always over a
// range and unbounded, weak eventually over a range, until, until_with, and
// the aborts.
TEST(CheckerVariableRandomization, ATemporalOperatorConstrainsLaterTicks) {
  ExpectAssumedPropertiesHold({"nexttime x", "x |-> nexttime [2] y",
                               "always [1:2] x", "always (x and nexttime y)",
                               "x |-> eventually [0:1] y", "x until y",
                               "x until_with y", "accept_on (z) x |-> ##1 y",
                               "reject_on (z) x |-> ##1 y"});
}

// The checker items `assumptions` leave x free: drawn at every posedge, it
// is 0 at some of them and 1 at others.
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

// §17.7.2 with §16.12.13: s_eventually fails at no time step, so assumed it
// leaves x free.
TEST(CheckerVariableRandomization, AnEventualityLeavesItsTickFree) {
  ExpectXDrawnFree("  m1: assume property (@(posedge clk) s_eventually x);\n");
}

// §17.7.2 with §16.7 and §16.9.2: an assumption over sequences whose
// matches span a varying number of ticks holds the attempt to the operands
// every way of going on reads at the time step: a delay over a range,
// bounded and not, consecutive repetition, bounded and not, goto and
// nonconsecutive repetition, and a range in an antecedent.
TEST(CheckerVariableRandomization, AVaryingSequenceConstrainsLaterTicks) {
  ExpectAssumedPropertiesHold({"x |-> ##[1:2] y", "x |-> ##[1:$] y",
                               "x |-> y[*2]", "x |-> y[*1:$] ##1 z",
                               "x |-> y[->1] ##1 z", "x |-> y[=1] ##1 z",
                               "x |-> y[->2:3] ##1 z", "x ##[0:1] y |-> z"});
}

// §17.7.2 with §16.12.1: an assumption's attempts are held to it only
// while its disable condition is false: x, free while rst is 1, is 0 at
// some of those posedges, and solved to 1 once rst falls, so that a1 never
// fails. Held to m1 regardless, x would be 1 throughout.
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

// §17.7.2 with §16.9.2.1: an operand repeated from zero may match empty,
// the delays on either side of it joined less a tick: first in a
// consequent, last in one, and last in a sequence assumed alone.
TEST(CheckerVariableRandomization, AnEmptyMatchConstrainsItsNeighbours) {
  ExpectAssumedPropertiesHold({"x |-> y[*0:1] ##1 z", "x |-> z ##[1:2] y[*0:1]",
                               "x ##1 y[*0:1] ##1 z"});
}

// §17.7.2 with §16.9.5 to §16.9.10: an assumption over sequences joined by
// or, and, intersect, first_match, throughout and within holds the attempt
// to every way of each operand that may still match, a group repeated
// among them, and a throughout over the whole chain or a part of it.
TEST(CheckerVariableRandomization, ASequenceOperatorConstrainsLaterTicks) {
  ExpectAssumedPropertiesHold(
      {"(x ##1 y or y ##1 x) |-> z", "(x ##1 y and y) |-> z",
       "(x ##[1:2] y intersect z ##1 1'b1) |-> y",
       "first_match(x ##[1:2] y) |-> z", "z throughout (x ##1 y) |-> ##1 y",
       "(x ##1 y) within (z ##3 z) |-> y", "x |-> (y ##1 z)[*2]",
       "x |-> (y or z ##1 y)[*1:2] ##1 z", "x ##1 (z throughout y ##1 y)",
       "(x ##1 (z throughout y)) |-> z"});
}

// §17.7.2 with §16.10: an assumption over a sequence assigning a local
// variable reads it later at the value the attempt assigned: y is solved
// to the value x had the tick before; through a compound assignment
// summing x over two ticks, to whether exactly one of them held; z to the
// parity of two locals one operand assigns; y through a local assigned
// under or and under and, the first nested in another sequence too; and x
// to differ from the local a repeated operand assigns at each repetition,
// consecutive, goto and nonconsecutive.
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
      "  sequence s7; bit v; (y, v = x)[->2] ##1 x != v; endsequence\n"
      "  sequence s8; bit v; (y, v = x)[=1] ##1 x != v; endsequence\n"

      "  sequence s2; bit [1:0] v; (1, v = x) ##1 (1, v += x) ##1 "
      "(y == (v == 2'd1)); endsequence\n");
}

// §17.7.2 with §16.13: an assumption whose operands name a clock of their
// own holds each attempt to them at the ticks of that clock, which are
// clock events of the assume set too: m2 holds y at 0 at each posedge, so
// only the attempts at the negedges can give it the values the negedge
// operands need -- a consequent, a sequence's operand, an if-else, a
// nexttime, an abort, a repetition, a goto and a throughout.
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

// §17.7.2 with §16.12.17: an assumption instantiating a named property
// holds the attempt to the declaration's body with the actuals, bound by
// position or by name, in the formals' places, a recursive property
// expanded a tick at a time, one declared with a clock read on it, and one
// declaring a local variable, which x reads a tick after y's value is
// assigned to it.
TEST(CheckerVariableRandomization, APropertyInstanceConstrainsItsBody) {
  ExpectAssumedPropertiesHold(
      {"p1(x, y)", "p1(.a(x), .b(y))", "p2", "p3", "p4"},
      "  property p1(a, b); a |-> ##1 b; endproperty\n"
      "  property p2; x and nexttime p2; endproperty\n"
      "  property p3; @(posedge clk) x |-> z; endproperty\n"
      "  property p4; bit v; (1, v = y) |=> x == v; endproperty\n");
}

}  // namespace
