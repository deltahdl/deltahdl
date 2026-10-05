#include <gtest/gtest.h>

#include <string>
#include <vector>

#include "fixture_vpi_run.h"
#include "simulator/sv_vpi_user.h"
#include "simulator/vpi_context.h"
#include "simulator/vpi_model_helpers1.h"
#include "simulator/vpi_object.h"
#include "simulator/vpi_user.h"

namespace delta {
namespace {

// §37.50 concurrent assertion: the VPI object model for a concurrent assertion.
// The concurrent-assertion class is realized by the
// assert/assume/cover/restrict directives; a concurrent assertion traverses to
// its clocking event (always the actual event, explicit or inferred), to its
// property (a property instance or specification), and - except for restrict -
// to its pass action statement; assert and assume additionally carry an else
// (fail) statement. A cover reports whether it covers a sequence, every
// assertion reports whether its clock was inferred, and a restrict is not
// simulated and so has no pass/fail statement and generates no run-time
// information. These tests observe the production helpers in vpi.cpp and the
// VpiContext methods that apply those rules.

// Claim 1: the four directive kinds the diagram draws are concurrent
// assertions; the immediate kinds and sequence/property instances (the broader
// §37.49 class) and unrelated kinds are not.
TEST(ConcurrentAssertionModel, ConcurrentAssertionTypeCoversTheFourDirectives) {
  EXPECT_TRUE(VpiIsConcurrentAssertionType(vpiAssert));
  EXPECT_TRUE(VpiIsConcurrentAssertionType(vpiAssume));
  EXPECT_TRUE(VpiIsConcurrentAssertionType(vpiCover));
  EXPECT_TRUE(VpiIsConcurrentAssertionType(vpiRestrict));

  EXPECT_FALSE(VpiIsConcurrentAssertionType(vpiImmediateAssert));
  EXPECT_FALSE(VpiIsConcurrentAssertionType(vpiSequenceInst));
  EXPECT_FALSE(VpiIsConcurrentAssertionType(vpiPropertyInst));
  EXPECT_FALSE(VpiIsConcurrentAssertionType(vpiModule));
}

// Claim 8: vpiProperty reaches a property instance or a property specification;
// no other kind is a concurrent assertion's property.
TEST(ConcurrentAssertionModel, PropertyRelationTargetKinds) {
  EXPECT_TRUE(VpiIsConcurrentAssertionPropertyType(vpiPropertyInst));
  EXPECT_TRUE(VpiIsConcurrentAssertionPropertyType(vpiPropertySpec));

  EXPECT_FALSE(VpiIsConcurrentAssertionPropertyType(vpiSequenceInst));
  EXPECT_FALSE(VpiIsConcurrentAssertionPropertyType(vpiOperation));
}

// Claim 8: an assertion traverses through vpiProperty to its property
// instance/specification child, and reports none when no property is attached.
TEST(ConcurrentAssertionModel, AssertionReachesItsProperty) {
  VpiObject assertion;
  assertion.type = vpiAssert;
  VpiObject spec;
  spec.type = vpiPropertySpec;
  assertion.children = {&spec};
  EXPECT_EQ(VpiConcurrentAssertionProperty(&assertion), &spec);

  VpiObject with_inst;
  with_inst.type = vpiAssume;
  VpiObject inst;
  inst.type = vpiPropertyInst;
  with_inst.children = {&inst};
  EXPECT_EQ(VpiConcurrentAssertionProperty(&with_inst), &inst);

  VpiObject bare;
  bare.type = vpiCover;
  EXPECT_EQ(VpiConcurrentAssertionProperty(&bare), nullptr);
  EXPECT_EQ(VpiConcurrentAssertionProperty(nullptr), nullptr);
}

// Claim 2 + Detail 1: the same clocking event is reported whether it was
// written explicitly or inferred; the vpiIsClockInferred Boolean is what
// distinguishes the two, not the clocking-event traversal. The event is the
// expression the assertion records as its clock.
TEST(ConcurrentAssertionModel, ClockingEventIsTheActualEventForBothForms) {
  VpiContext ctx;

  VpiObject explicit_clk;
  explicit_clk.type = vpiAssert;
  VpiObject ev0;
  ev0.type = vpiOperation;
  explicit_clk.clocking_event = &ev0;
  EXPECT_EQ(VpiConcurrentAssertionClockingEvent(&explicit_clk), &ev0);
  EXPECT_EQ(ctx.Get(vpiIsClockInferred, &explicit_clk), 0);

  VpiObject inferred_clk;
  inferred_clk.type = vpiAssert;
  inferred_clk.clock_inferred = true;
  VpiObject ev1;
  ev1.type = vpiOperation;
  inferred_clk.clocking_event = &ev1;
  EXPECT_EQ(VpiConcurrentAssertionClockingEvent(&inferred_clk), &ev1);
  EXPECT_EQ(ctx.Get(vpiIsClockInferred, &inferred_clk), 1);
}

// Claim 2 edge: an assertion with no clocking event, and a null handle, report
// no clocking event.
TEST(ConcurrentAssertionModel, MissingClockingEventReportsNull) {
  VpiObject assertion;
  assertion.type = vpiAssume;
  EXPECT_EQ(VpiConcurrentAssertionClockingEvent(&assertion), nullptr);
  EXPECT_EQ(VpiConcurrentAssertionClockingEvent(nullptr), nullptr);
}

// Claim 4: a cover reports whether it covers a sequence through
// vpi_get(vpiIsCoverSequence).
TEST(ConcurrentAssertionModel, CoverReportsIsCoverSequence) {
  VpiContext ctx;
  VpiObject seq_cover;
  seq_cover.type = vpiCover;
  seq_cover.cover_sequence = true;
  EXPECT_EQ(ctx.Get(vpiIsCoverSequence, &seq_cover), 1);

  VpiObject prop_cover;
  prop_cover.type = vpiCover;
  EXPECT_EQ(ctx.Get(vpiIsCoverSequence, &prop_cover), 0);
}

// Claim 4 "false otherwise": vpiIsCoverSequence is meaningful only for a cover,
// so a concurrent assertion of a different kind (here an assert) reports 0 for
// the same property - the other input kind for the same query.
TEST(ConcurrentAssertionModel, NonCoverReportsIsCoverSequenceFalse) {
  VpiContext ctx;
  VpiObject assertion;
  assertion.type = vpiAssert;
  EXPECT_EQ(ctx.Get(vpiIsCoverSequence, &assertion), 0);

  VpiObject assume_obj;
  assume_obj.type = vpiAssume;
  EXPECT_EQ(ctx.Get(vpiIsCoverSequence, &assume_obj), 0);
}

// Claim 3 + Detail 2: assert, assume and cover carry a pass action statement; a
// restrict has none.
TEST(ConcurrentAssertionModel, PassStatementPresenceByKind) {
  EXPECT_TRUE(VpiConcurrentAssertionHasPassStmt(vpiAssert));
  EXPECT_TRUE(VpiConcurrentAssertionHasPassStmt(vpiAssume));
  EXPECT_TRUE(VpiConcurrentAssertionHasPassStmt(vpiCover));
  EXPECT_FALSE(VpiConcurrentAssertionHasPassStmt(vpiRestrict));
}

// Claim 5 + Detail 2: only assert and assume carry an else (fail) statement; a
// cover has no else statement and a restrict has no fail statement.
TEST(ConcurrentAssertionModel, ElseStatementPresenceByKind) {
  EXPECT_TRUE(VpiConcurrentAssertionHasElseStmt(vpiAssert));
  EXPECT_TRUE(VpiConcurrentAssertionHasElseStmt(vpiAssume));
  EXPECT_FALSE(VpiConcurrentAssertionHasElseStmt(vpiCover));
  EXPECT_FALSE(VpiConcurrentAssertionHasElseStmt(vpiRestrict));
}

// Claims 3 and 5: an assert traverses to its pass statement through vpiStmt and
// to its else statement through vpiElseStmt; each is null when absent. A
// statement's own type is a statement kind, so the two are told apart by the
// else action the assertion records and by position.
TEST(ConcurrentAssertionModel, AssertReachesPassAndElseStatements) {
  VpiObject assertion;
  assertion.type = vpiAssert;
  VpiObject pass;
  pass.type = vpiAssignment;
  VpiObject els;
  els.type = vpiAssignment;
  assertion.children = {&pass, &els};
  assertion.else_stmt = &els;
  EXPECT_EQ(VpiConcurrentAssertionStmt(&assertion), &pass);
  EXPECT_EQ(VpiConcurrentAssertionElseStmt(&assertion), &els);

  // A cover draws no else edge, however many statements it holds.
  VpiObject pass_only;
  pass_only.type = vpiCover;
  VpiObject p2;
  p2.type = vpiAssignment;
  VpiObject p3;
  p3.type = vpiAssignment;
  pass_only.children = {&p2, &p3};
  EXPECT_EQ(VpiConcurrentAssertionStmt(&pass_only), &p2);
  EXPECT_EQ(VpiConcurrentAssertionElseStmt(&pass_only), nullptr);

  // A fail action written alone is no pass action.
  VpiObject fail_only;
  fail_only.type = vpiAssume;
  VpiObject f;
  f.type = vpiAssignment;
  fail_only.children = {&f};
  fail_only.else_stmt = &f;
  EXPECT_EQ(VpiConcurrentAssertionStmt(&fail_only), nullptr);
  EXPECT_EQ(VpiConcurrentAssertionElseStmt(&fail_only), &f);

  EXPECT_EQ(VpiConcurrentAssertionStmt(nullptr), nullptr);
  EXPECT_EQ(VpiConcurrentAssertionElseStmt(nullptr), nullptr);
}

// Detail 2: a restrict is not simulated and so generates no run-time
// information; the other concurrent assertion kinds are simulated.
TEST(ConcurrentAssertionModel, RestrictIsNotSimulated) {
  EXPECT_FALSE(VpiConcurrentAssertionIsSimulated(vpiRestrict));

  EXPECT_TRUE(VpiConcurrentAssertionIsSimulated(vpiAssert));
  EXPECT_TRUE(VpiConcurrentAssertionIsSimulated(vpiAssume));
  EXPECT_TRUE(VpiConcurrentAssertionIsSimulated(vpiCover));

  // A non-concurrent-assertion kind is not a simulated concurrent assertion.
  EXPECT_FALSE(VpiConcurrentAssertionIsSimulated(vpiModule));
}

// Claim 6: a concurrent assertion exposes its name and full name through
// vpi_get_str(vpiName/vpiFullName).
TEST(ConcurrentAssertionModel, AssertionReportsNameAndFullName) {
  VpiContext ctx;
  std::string name = "req_ack";
  VpiObject assertion;
  assertion.type = vpiAssert;
  assertion.name = name;
  assertion.full_name = "top.u_dut.req_ack";

  EXPECT_STREQ(ctx.GetStr(vpiName, &assertion), "req_ack");
  EXPECT_STREQ(ctx.GetStr(vpiFullName, &assertion), "top.u_dut.req_ack");
}

// Claim 8 edge: the property traversal matches by kind, so an assertion whose
// only child is an unrelated object reaches no property.
TEST(ConcurrentAssertionModel, PropertyTraversalSkipsNonPropertyChildren) {
  VpiObject assertion;
  assertion.type = vpiAssert;
  VpiObject net_child;
  net_child.type = vpiNet;
  assertion.children = {&net_child};
  EXPECT_EQ(VpiConcurrentAssertionProperty(&assertion), nullptr);
}

// Claim 2 edge: the clocking event is the expression the assertion records,
// so an assertion carrying an event control among its children reports none.
TEST(ConcurrentAssertionModel, ClockingEventIsNoChildOfTheAssertion) {
  VpiObject assertion;
  assertion.type = vpiAssume;
  VpiObject control;
  control.type = vpiEventControl;
  assertion.children = {&control};
  EXPECT_EQ(VpiConcurrentAssertionClockingEvent(&assertion), nullptr);
}

// Claims 3 and 5 edge: the pass- and else-statement traversals each match their
// own statement child, so an assertion with only unrelated children reaches
// neither a pass nor an else statement.
TEST(ConcurrentAssertionModel, StatementTraversalsSkipNonStatementChildren) {
  VpiObject assertion;
  assertion.type = vpiAssert;
  VpiObject net_child;
  net_child.type = vpiNet;
  assertion.children = {&net_child};
  EXPECT_EQ(VpiConcurrentAssertionStmt(&assertion), nullptr);
  EXPECT_EQ(VpiConcurrentAssertionElseStmt(&assertion), nullptr);
}

class ConcurrentAssertionsOfARun : public VpiDesignRun {
 protected:
  // The name of what `relation` reaches from `ref`, empty for nothing.
  static std::string NameReached(int relation, vpiHandle ref) {
    vpiHandle reached = ref == nullptr ? nullptr : vpi_handle(relation, ref);
    return reached == nullptr ? "" : vpi_get_str(vpiName, reached);
  }

  // The edge operation `event` stands for and the name of what it is taken
  // of, as "posedge clk"; empty where it is no edge operation.
  static std::string EdgeOf(vpiHandle event) {
    if (event == nullptr || vpi_get(vpiType, event) != vpiOperation) return "";
    const int kOp = vpi_get(vpiOpType, event);
    vpiHandle operands = vpi_iterate(vpiOperand, event);
    vpiHandle operand = operands == nullptr ? nullptr : vpi_scan(operands);
    if (operand == nullptr) return "";
    const std::string kName = vpi_get_str(vpiName, operand);
    if (kOp == vpiPosedgeOp) return "posedge " + kName;
    return kOp == vpiNegedgeOp ? "negedge " + kName : "";
  }
};

// An assertion written as an item reaches its pass action through vpiStmt and
// its fail action through vpiElseStmt (#5079).
TEST_F(ConcurrentAssertionsOfARun, AnItemReachesBothActions) {
  Run("module top; logic clk, a;\n"
      "  a1: assert property (@(posedge clk) a) $display(\"p\");\n"
      "      else $write(\"f\");\n"
      "  c1: cover property (@(posedge clk) a) $display(\"c\");\n"
      "endmodule\n");
  vpiHandle a1 = Named(vpiAssertion, By("top"), "a1");
  vpiHandle c1 = Named(vpiAssertion, By("top"), "c1");
  ASSERT_NE(a1, nullptr);
  ASSERT_NE(c1, nullptr);
  EXPECT_EQ(NameReached(vpiStmt, a1), "$display");
  EXPECT_EQ(NameReached(vpiElseStmt, a1), "$write");
  EXPECT_EQ(NameReached(vpiStmt, c1), "$display");
  EXPECT_EQ(NameReached(vpiElseStmt, c1), "");
}

// A fail action written alone is reached through vpiElseStmt and is no pass
// action (#5079).
TEST_F(ConcurrentAssertionsOfARun, AFailActionAloneIsTheElseStatement) {
  Run("module top; logic clk, a;\n"
      "  a1: assert property (@(posedge clk) a) else $write(\"f\");\n"
      "endmodule\n");
  vpiHandle a1 = Named(vpiAssertion, By("top"), "a1");
  ASSERT_NE(a1, nullptr);
  EXPECT_EQ(NameReached(vpiStmt, a1), "");
  EXPECT_EQ(NameReached(vpiElseStmt, a1), "$write");
}

// An assertion embedded in a procedure reaches its actions the same way
// (#5079).
TEST_F(ConcurrentAssertionsOfARun, AProceduralAssertionReachesBothActions) {
  Run("module top; logic clk, a;\n"
      "  always @(posedge clk)\n"
      "    p1: assert property (a) $display(\"p\"); else $write(\"f\");\n"
      "endmodule\n");
  vpiHandle p1 = Named(vpiAssertion, By("top"), "p1");
  ASSERT_NE(p1, nullptr);
  EXPECT_EQ(NameReached(vpiStmt, p1), "$display");
  EXPECT_EQ(NameReached(vpiElseStmt, p1), "$write");
}

// An assertion reaches the clock it writes through vpiClockingEvent, which was
// not inferred (#5080).
TEST_F(ConcurrentAssertionsOfARun, AnAssertionReachesTheClockItWrites) {
  Run("module top; logic clk, a;\n"
      "  a1: assert property (@(posedge clk) a);\n"
      "endmodule\n");
  vpiHandle a1 = Named(vpiAssertion, By("top"), "a1");
  ASSERT_NE(a1, nullptr);
  EXPECT_EQ(EdgeOf(vpi_handle(vpiClockingEvent, a1)), "posedge clk");
  EXPECT_EQ(vpi_get(vpiIsClockInferred, a1), 0);
}

// An assertion writing no clock reaches the default clocking's event, inferred
// (§16.16), and one embedded in a procedure the procedure's (§16.14.6) (#5080).
TEST_F(ConcurrentAssertionsOfARun, AnInferredClockIsReachedAndReported) {
  Run("module top; logic clk, a;\n"
      "  default clocking cb @(negedge clk); endclocking\n"
      "  a1: assert property (a);\n"
      "  always @(posedge clk) p1: assert property (a);\n"
      "endmodule\n");
  vpiHandle a1 = Named(vpiAssertion, By("top"), "a1");
  vpiHandle p1 = Named(vpiAssertion, By("top"), "p1");
  ASSERT_NE(a1, nullptr);
  ASSERT_NE(p1, nullptr);
  EXPECT_EQ(EdgeOf(vpi_handle(vpiClockingEvent, a1)), "negedge clk");
  EXPECT_EQ(vpi_get(vpiIsClockInferred, a1), 1);
  EXPECT_EQ(EdgeOf(vpi_handle(vpiClockingEvent, p1)), "posedge clk");
  EXPECT_EQ(vpi_get(vpiIsClockInferred, p1), 1);
}

// An assertion reaches its property spec through vpiProperty, and the spec its
// clock, its disable condition and its property expression (#5081).
TEST_F(ConcurrentAssertionsOfARun, AnAssertionReachesItsPropertySpec) {
  Run("module top; logic clk, rst, a;\n"
      "  a1: assert property (@(posedge clk) disable iff (rst) a);\n"
      "endmodule\n");
  vpiHandle a1 = Named(vpiAssertion, By("top"), "a1");
  ASSERT_NE(a1, nullptr);
  vpiHandle spec = vpi_handle(vpiProperty, a1);
  ASSERT_NE(spec, nullptr);
  EXPECT_EQ(vpi_get(vpiType, spec), vpiPropertySpec);
  EXPECT_EQ(EdgeOf(vpi_handle(vpiClockingEvent, spec)), "posedge clk");
  EXPECT_EQ(NameReached(vpiDisableCondition, spec), "rst");
  EXPECT_EQ(NameReached(vpiPropertyExpr, spec), "a");
}

// A spec that is a name declaring no property is a Boolean property spec, on
// the default clocking's event as though written (§16.16) (#5081).
TEST_F(ConcurrentAssertionsOfARun, ABareNameIsABooleanPropertySpec) {
  Run("module top; logic clk, a;\n"
      "  default clocking cb @(negedge clk); endclocking\n"
      "  a1: assert property (a);\n"
      "endmodule\n");
  vpiHandle a1 = Named(vpiAssertion, By("top"), "a1");
  ASSERT_NE(a1, nullptr);
  vpiHandle spec = vpi_handle(vpiProperty, a1);
  ASSERT_NE(spec, nullptr);
  EXPECT_EQ(vpi_get(vpiType, spec), vpiPropertySpec);
  EXPECT_EQ(EdgeOf(vpi_handle(vpiClockingEvent, spec)), "negedge clk");
  EXPECT_EQ(NameReached(vpiPropertyExpr, spec), "a");
}

// A restrict property reaches the clock it writes, or the default clocking's
// inferred, and its property spec, as any concurrent assertion does, though
// the run never checks it (§16.14.4) (#5088).
TEST_F(ConcurrentAssertionsOfARun, ARestrictReachesItsClockAndPropertySpec) {
  Run("module top; logic clk, a;\n"
      "  default clocking cb @(negedge clk); endclocking\n"
      "  r1: restrict property (@(posedge clk) a);\n"
      "  r2: restrict property (a);\n"
      "endmodule\n");
  vpiHandle r1 = Named(vpiAssertion, By("top"), "r1");
  vpiHandle r2 = Named(vpiAssertion, By("top"), "r2");
  ASSERT_NE(r1, nullptr);
  ASSERT_NE(r2, nullptr);
  EXPECT_EQ(EdgeOf(vpi_handle(vpiClockingEvent, r1)), "posedge clk");
  EXPECT_EQ(vpi_get(vpiIsClockInferred, r1), 0);
  EXPECT_EQ(EdgeOf(vpi_handle(vpiClockingEvent, r2)), "negedge clk");
  EXPECT_EQ(vpi_get(vpiIsClockInferred, r2), 1);
  vpiHandle spec = vpi_handle(vpiProperty, r1);
  ASSERT_NE(spec, nullptr);
  EXPECT_EQ(vpi_get(vpiType, spec), vpiPropertySpec);
  EXPECT_EQ(NameReached(vpiPropertyExpr, spec), "a");
}

// An assertion on $global_clock reaches the event the global clocking
// declaration its instance resolves to names (§16.5.2, §14.14), each instance
// of one module its own (#5089).
TEST_F(ConcurrentAssertionsOfARun, AGlobalClockIsTheEventItsInstanceResolves) {
  Run("module child(input logic clk, a);\n"
      "  a1: assert property (@$global_clock a);\n"
      "endmodule\n"
      "module rise(input logic clk, a);\n"
      "  global clocking @(posedge clk); endclocking\n"
      "  child c(clk, a);\n"
      "endmodule\n"
      "module fall(input logic clk, a);\n"
      "  global clocking @(negedge clk); endclocking\n"
      "  child c(clk, a);\n"
      "endmodule\n"
      "module top; logic clk, a;\n"
      "  rise u1(clk, a);\n"
      "  fall u2(clk, a);\n"
      "endmodule\n");
  vpiHandle up = Named(vpiAssertion, By("top.u1.c"), "a1");
  vpiHandle down = Named(vpiAssertion, By("top.u2.c"), "a1");
  ASSERT_NE(up, nullptr);
  ASSERT_NE(down, nullptr);
  vpiHandle rising = vpi_handle(vpiClockingEvent, up);
  vpiHandle falling = vpi_handle(vpiClockingEvent, down);
  ASSERT_NE(rising, nullptr);
  ASSERT_NE(falling, nullptr);
  EXPECT_EQ(vpi_get(vpiOpType, rising), vpiPosedgeOp);
  EXPECT_EQ(vpi_get(vpiOpType, falling), vpiNegedgeOp);
}

// One embedded in a procedure is clocked the same way (#5089).
TEST_F(ConcurrentAssertionsOfARun, AProceduralGlobalClockIsTheDeclaredEvent) {
  Run("module top; logic clk, a;\n"
      "  global clocking @(negedge clk); endclocking\n"
      "  always @(posedge clk) p1: assert property (@$global_clock a);\n"
      "endmodule\n");
  vpiHandle p1 = Named(vpiAssertion, By("top"), "p1");
  ASSERT_NE(p1, nullptr);
  EXPECT_EQ(EdgeOf(vpi_handle(vpiClockingEvent, p1)), "negedge clk");
  EXPECT_EQ(vpi_get(vpiIsClockInferred, p1), 0);
}

}  // namespace
}  // namespace delta
