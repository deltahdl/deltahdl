#include <gtest/gtest.h>

#include <string>
#include <vector>

#include "fixture_vpi_run.h"
#include "simulator/sv_vpi_user.h"
#include "simulator/vpi_context.h"
#include "simulator/vpi_globals.h"
#include "simulator/vpi_model_helpers1.h"
#include "simulator/vpi_object.h"
#include "simulator/vpi_user.h"

namespace delta {
namespace {

// §37.65 Event control: the object model diagram draws an event control "@"
// object with a vpiCondition relation (to an expression, a sequence instance,
// or a named event) and a vpiStmt edge to a statement. The clause's sole
// numbered Detail (D1) governs that statement edge: when the event control is
// associated with an assignment, the statement shall always be NULL. These
// tests observe the production code that applies both relations - the
// vpiCondition operand reached by VpiEventControlConditionExpr, and the
// vpiStmt/D1 edge applied by VpiEventControlStmt - directly and through the
// public vpi_handle(...) dispatch path.
//
// The statement objects below carry the kinds §37.4.1's dotted `stmt` class
// groups rather than vpiStmt itself: that enclosure is a class grouping other
// objects, so no statement of a design has the relation's tag for its own kind,
// and a scan that asked for one found the guarded statement of no timing
// control any design could hold.

// The fixture installs a context so the public vpi_handle entry point runs its
// real dispatch over the test objects.
class EventControl : public ::testing::Test {
 protected:
  void SetUp() override { SetGlobalVpiContext(&ctx_); }
  void TearDown() override { SetGlobalVpiContext(nullptr); }
  VpiContext ctx_;
};

// D1 (complement): an event control that is not associated with an assignment
// reaches its guarded statement normally - the rule is specific to the
// assignment association and does not blanket-null every event control's stmt.
TEST_F(EventControl, StandaloneEventControlReachesItsStatement) {
  VpiObject stmt;
  stmt.type = vpiBegin;

  VpiObject event_control;
  event_control.type = vpiEventControl;
  event_control.children = {&stmt};

  EXPECT_EQ(VpiEventControlStmt(&event_control), &stmt);

  // A non-assignment parent (here the event control sits inside an event
  // statement) is still an ordinary event control, so the statement is reached.
  VpiObject event_stmt;
  event_stmt.type = vpiEventStmt;
  event_control.parent = &event_stmt;
  EXPECT_EQ(VpiEventControlStmt(&event_control), &stmt);
}

// D1 edge: a null handle and an event control with no statement child both
// report no statement.
TEST_F(EventControl, NullAndEmptyEventControlsReportNoStatement) {
  EXPECT_EQ(VpiEventControlStmt(nullptr), nullptr);

  VpiObject bare;
  bare.type = vpiEventControl;
  EXPECT_EQ(VpiEventControlStmt(&bare), nullptr);
}

// Condition edge: a null handle reports no condition, as it reports no
// statement above.
TEST_F(EventControl, NullEventControlReportsNoCondition) {
  EXPECT_EQ(VpiEventControlConditionExpr(nullptr), nullptr);
}

// D1 end to end: the rule is applied by the public vpi_handle(vpiStmt, ...)
// dispatch. The assignment-associated event control yields a null statement,
// while a standalone event control yields its statement child through the same
// entry point.
TEST_F(EventControl, RuleAppliesThroughPublicVpiHandleDispatch) {
  VpiObject guarded;
  guarded.type = vpiBegin;

  VpiObject assignment;
  assignment.type = vpiAssignment;

  VpiObject on_assignment;
  on_assignment.type = vpiEventControl;
  on_assignment.parent = &assignment;
  on_assignment.children = {&guarded};
  EXPECT_EQ(vpi_handle(vpiStmt, VpiHandleOf(&on_assignment)), nullptr);

  VpiObject standalone;
  standalone.type = vpiEventControl;
  standalone.children = {&guarded};
  EXPECT_EQ(VpiObjectOf(vpi_handle(vpiStmt, VpiHandleOf(&standalone))),
            &guarded);
}

// C1 (vpiCondition): the event control diagram draws a vpiCondition edge to an
// expression, a sequence instance, or a named event. The relation is applied by
// the public vpi_handle(vpiCondition, ...) dispatch, and it reaches whichever
// of those three condition operand kinds the event control carries - one input
// form per source shape ("@(a or b)", "@(seq)", "@ev").
TEST_F(EventControl, ConditionRelationReachesEachEventOperandKind) {
  // "@(a or b)": an ordinary expression operand.
  VpiObject expr_cond;
  expr_cond.type = vpiOperation;
  VpiObject on_expr;
  on_expr.type = vpiEventControl;
  on_expr.children = {&expr_cond};
  EXPECT_EQ(VpiObjectOf(vpi_handle(vpiCondition, VpiHandleOf(&on_expr))),
            &expr_cond);

  // "@(seq)": a sequence instance operand.
  VpiObject seq_cond;
  seq_cond.type = vpiSequenceInst;
  VpiObject on_seq;
  on_seq.type = vpiEventControl;
  on_seq.children = {&seq_cond};
  EXPECT_EQ(VpiObjectOf(vpi_handle(vpiCondition, VpiHandleOf(&on_seq))),
            &seq_cond);

  // "@ev": a named event operand.
  VpiObject named_cond;
  named_cond.type = vpiNamedEvent;
  VpiObject on_named;
  on_named.type = vpiEventControl;
  on_named.children = {&named_cond};
  EXPECT_EQ(VpiObjectOf(vpi_handle(vpiCondition, VpiHandleOf(&on_named))),
            &named_cond);
}

// C1 (negative): the condition scan admits only the three operand kinds, so an
// event control that carries only its guarded body statement - and no condition
// operand - reports no condition. This confirms the vpiStmt body edge is not
// mistaken for the vpiCondition operand.
TEST_F(EventControl, ConditionRelationIgnoresGuardedStatement) {
  VpiObject body;
  body.type = vpiBegin;

  VpiObject event_control;
  event_control.type = vpiEventControl;
  event_control.children = {&body};

  EXPECT_EQ(vpi_handle(vpiCondition, VpiHandleOf(&event_control)), nullptr);
}

// The event controls of a run: those a design's procedures write, built from
// the elaborated design rather than by hand (#4999).
class EventControlsOfARun : public VpiDesignRun {
 protected:
  // The statement the first procedure of `scope` runs.
  static vpiHandle BodyOf(const std::string& scope) {
    vpiHandle it = vpi_iterate(vpiProcess, By(scope));
    return it == nullptr ? nullptr : vpi_handle(vpiStmt, vpi_scan(it));
  }

  // The operands of the operation `op`, in order.
  static std::vector<vpiHandle> OperandsOf(vpiHandle op) {
    std::vector<vpiHandle> operands;
    vpiHandle it = vpi_iterate(vpiOperand, op);
    if (it == nullptr) return operands;
    while (vpiHandle operand = vpi_scan(it)) operands.push_back(operand);
    return operands;
  }
};

// An event control a procedure writes is an object of the run, written over
// the posedge operation of the variable it names and guarding the statement
// written after it, which stands in the instance and runs in the procedure.
TEST_F(EventControlsOfARun, AnEventControlIsAnObjectOfTheRun) {
  Run("module top; bit clk; int q, d; always @(posedge clk) q <= d;\n"
      "endmodule\n");
  vpiHandle control = BodyOf("top");
  ASSERT_NE(control, nullptr);
  EXPECT_EQ(vpi_get(vpiType, control), vpiEventControl);
  vpiHandle condition = vpi_handle(vpiCondition, control);
  ASSERT_NE(condition, nullptr);
  EXPECT_EQ(vpi_get(vpiOpType, condition), vpiPosedgeOp);
  const std::vector<vpiHandle> kOperands = OperandsOf(condition);
  ASSERT_EQ(kOperands.size(), 1U);
  EXPECT_EQ(VpiObjectOf(kOperands[0]), VpiObjectOf(By("top.clk")));
  vpiHandle guarded = vpi_handle(vpiStmt, control);
  ASSERT_NE(guarded, nullptr);
  EXPECT_EQ(vpi_get(vpiType, guarded), vpiAssignment);
  EXPECT_EQ(vpi_get(vpiBlocking, guarded), 0);
  EXPECT_EQ(VpiObjectOf(vpi_handle(vpiScope, guarded)), VpiObjectOf(By("top")));
  EXPECT_EQ(VpiObjectOf(vpi_handle(vpiProcess, guarded)),
            VpiObjectOf(vpi_handle(vpiProcess, control)));
}

// A bare named event is the condition itself, the object its declaration
// stands as.
TEST_F(EventControlsOfARun, ANamedEventIsTheConditionItself) {
  Run("module top; event e; initial @e ; endmodule\n");
  vpiHandle control = BodyOf("top");
  ASSERT_NE(control, nullptr);
  vpiHandle condition = vpi_handle(vpiCondition, control);
  ASSERT_NE(condition, nullptr);
  EXPECT_EQ(vpi_get(vpiType, condition), vpiNamedEvent);
  EXPECT_EQ(VpiObjectOf(condition), VpiObjectOf(By("top.e")));
  vpiHandle guarded = vpi_handle(vpiStmt, control);
  ASSERT_NE(guarded, nullptr);
  EXPECT_EQ(vpi_get(vpiType, guarded), vpiNullStmt);
}

// §9.4.2.1 joins a list's events with `or`, a comma meaning the same, each
// `or` nested around the events before it; an event an iff guards is the iff
// operation of the event and its condition.
TEST_F(EventControlsOfARun, AnEventListIsAnEventOrOperation) {
  Run("module top; bit a, b, c, en;\n"
      "  initial @(c, posedge a iff en or b) ;\n"
      "endmodule\n");
  vpiHandle control = BodyOf("top");
  ASSERT_NE(control, nullptr);
  vpiHandle outer = vpi_handle(vpiCondition, control);
  ASSERT_NE(outer, nullptr);
  EXPECT_EQ(vpi_get(vpiOpType, outer), vpiEventOrOp);
  const std::vector<vpiHandle> kOuter = OperandsOf(outer);
  ASSERT_EQ(kOuter.size(), 2U);
  EXPECT_EQ(VpiObjectOf(kOuter[1]), VpiObjectOf(By("top.b")));
  EXPECT_EQ(vpi_get(vpiOpType, kOuter[0]), vpiEventOrOp);
  const std::vector<vpiHandle> kInner = OperandsOf(kOuter[0]);
  ASSERT_EQ(kInner.size(), 2U);
  EXPECT_EQ(VpiObjectOf(kInner[0]), VpiObjectOf(By("top.c")));
  EXPECT_EQ(vpi_get(vpiOpType, kInner[1]), vpiIffOp);
  const std::vector<vpiHandle> kIff = OperandsOf(kInner[1]);
  ASSERT_EQ(kIff.size(), 2U);
  EXPECT_EQ(vpi_get(vpiOpType, kIff[0]), vpiPosedgeOp);
  EXPECT_EQ(VpiObjectOf(kIff[1]), VpiObjectOf(By("top.en")));
}

// The implicit event list of §9.4.2.2 writes no condition, while the control
// still guards its statement.
TEST_F(EventControlsOfARun, AnImplicitEventListWritesNoCondition) {
  Run("module top; int a, b; always @* a = b; endmodule\n");
  vpiHandle control = BodyOf("top");
  ASSERT_NE(control, nullptr);
  EXPECT_EQ(vpi_get(vpiType, control), vpiEventControl);
  EXPECT_EQ(vpi_handle(vpiCondition, control), nullptr);
  vpiHandle guarded = vpi_handle(vpiStmt, control);
  ASSERT_NE(guarded, nullptr);
  EXPECT_EQ(vpi_get(vpiType, guarded), vpiAssignment);
}

}  // namespace
}  // namespace delta
