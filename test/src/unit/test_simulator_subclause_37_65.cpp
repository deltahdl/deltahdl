#include <gtest/gtest.h>

#include "simulator/sv_vpi_user.h"
#include "simulator/vpi.h"

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
  stmt.type = vpiStmt;

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

// D1 end to end: the rule is applied by the public vpi_handle(vpiStmt, ...)
// dispatch. The assignment-associated event control yields a null statement,
// while a standalone event control yields its statement child through the same
// entry point.
TEST_F(EventControl, RuleAppliesThroughPublicVpiHandleDispatch) {
  VpiObject guarded;
  guarded.type = vpiStmt;

  VpiObject assignment;
  assignment.type = vpiAssignment;

  VpiObject on_assignment;
  on_assignment.type = vpiEventControl;
  on_assignment.parent = &assignment;
  on_assignment.children = {&guarded};
  EXPECT_EQ(vpi_handle(vpiStmt, &on_assignment), nullptr);

  VpiObject standalone;
  standalone.type = vpiEventControl;
  standalone.children = {&guarded};
  EXPECT_EQ(vpi_handle(vpiStmt, &standalone), &guarded);
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
  EXPECT_EQ(vpi_handle(vpiCondition, &on_expr), &expr_cond);

  // "@(seq)": a sequence instance operand.
  VpiObject seq_cond;
  seq_cond.type = vpiSequenceInst;
  VpiObject on_seq;
  on_seq.type = vpiEventControl;
  on_seq.children = {&seq_cond};
  EXPECT_EQ(vpi_handle(vpiCondition, &on_seq), &seq_cond);

  // "@ev": a named event operand.
  VpiObject named_cond;
  named_cond.type = vpiNamedEvent;
  VpiObject on_named;
  on_named.type = vpiEventControl;
  on_named.children = {&named_cond};
  EXPECT_EQ(vpi_handle(vpiCondition, &on_named), &named_cond);
}

// C1 (negative): the condition scan admits only the three operand kinds, so an
// event control that carries only its guarded body statement - and no condition
// operand - reports no condition. This confirms the vpiStmt body edge is not
// mistaken for the vpiCondition operand.
TEST_F(EventControl, ConditionRelationIgnoresGuardedStatement) {
  VpiObject body;
  body.type = vpiStmt;

  VpiObject event_control;
  event_control.type = vpiEventControl;
  event_control.children = {&body};

  EXPECT_EQ(vpi_handle(vpiCondition, &event_control), nullptr);
}

}  // namespace
}  // namespace delta
