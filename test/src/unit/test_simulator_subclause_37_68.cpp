#include <gtest/gtest.h>

#include "simulator/sv_vpi_user.h"
#include "simulator/vpi.h"

namespace delta {
namespace {

// §37.68 Delay control: the object model diagram draws a delay control "#"
// object with a vpiDelay relation (to an expression, plus the delay set reached
// via vpi_get_delays(), §38.10) and a vpiStmt edge to a statement. The clause's
// sole numbered Detail (D1) governs that statement edge: when the delay control
// is associated with an assignment, the statement shall always be NULL. These
// tests observe the production code that applies that rule
// (VpiDelayControlStmt) both directly and through the public
// vpi_handle(vpiStmt, ...) dispatch path.

// The fixture installs a context so the public vpi_handle entry point runs its
// real dispatch over the test objects.
class DelayControl : public ::testing::Test {
 protected:
  void SetUp() override { SetGlobalVpiContext(&ctx_); }
  void TearDown() override { SetGlobalVpiContext(nullptr); }
  VpiContext ctx_;
};

// D1 (complement): a delay control that is not associated with an assignment
// reaches its guarded statement normally - the rule is specific to the
// assignment association and does not blanket-null every delay control's stmt.
TEST_F(DelayControl, StandaloneDelayControlReachesItsStatement) {
  VpiObject stmt;
  stmt.type = vpiStmt;

  VpiObject delay_control;
  delay_control.type = vpiDelayControl;
  delay_control.children = {&stmt};

  EXPECT_EQ(VpiDelayControlStmt(&delay_control), &stmt);

  // A non-assignment parent (here the delay control sits inside an ordinary
  // procedural statement) is still an ordinary delay control, so the statement
  // is reached.
  VpiObject host_stmt;
  host_stmt.type = vpiStmt;
  delay_control.parent = &host_stmt;
  EXPECT_EQ(VpiDelayControlStmt(&delay_control), &stmt);
}

// D1 edge: a null handle and a delay control with no statement child both
// report no statement.
TEST_F(DelayControl, NullAndEmptyDelayControlsReportNoStatement) {
  EXPECT_EQ(VpiDelayControlStmt(nullptr), nullptr);

  VpiObject bare;
  bare.type = vpiDelayControl;
  EXPECT_EQ(VpiDelayControlStmt(&bare), nullptr);
}

// D1 end to end: the rule is applied by the public vpi_handle(vpiStmt, ...)
// dispatch. The assignment-associated delay control yields a null statement,
// while a standalone delay control yields its statement child through the same
// entry point.
TEST_F(DelayControl, RuleAppliesThroughPublicVpiHandleDispatch) {
  VpiObject guarded;
  guarded.type = vpiStmt;

  VpiObject assignment;
  assignment.type = vpiAssignment;

  VpiObject on_assignment;
  on_assignment.type = vpiDelayControl;
  on_assignment.parent = &assignment;
  on_assignment.children = {&guarded};
  EXPECT_EQ(vpi_handle(vpiStmt, &on_assignment), nullptr);

  VpiObject standalone;
  standalone.type = vpiDelayControl;
  standalone.children = {&guarded};
  EXPECT_EQ(vpi_handle(vpiStmt, &standalone), &guarded);
}

// vpiDelay: a delay control reaches its "#" delay expression through vpiDelay.
// The delay operand is the delay control's expression child; the guarded
// statement child (a vpiStmt) is skipped. Observed through the public
// vpi_handle(vpiDelay, ...) dispatch that calls VpiDelayControlDelayExpr.
TEST_F(DelayControl, DelayControlReachesItsDelayExpressionThroughVpiDelay) {
  VpiObject delay_expr;
  delay_expr.type = vpiConstant;  // e.g. the "5" in "#5 stmt;"

  VpiObject guarded;
  guarded.type = vpiStmt;

  VpiObject delay_control;
  delay_control.type = vpiDelayControl;
  // The guarded statement precedes the delay operand in child order to prove
  // the scan selects on expression kind, not on position.
  delay_control.children = {&guarded, &delay_expr};

  EXPECT_EQ(vpi_handle(vpiDelay, &delay_control), &delay_expr);
  EXPECT_EQ(VpiDelayControlDelayExpr(&delay_control), &delay_expr);
}

// vpiDelay holds even for an intra-assignment delay control ("x = #5 y"): its
// guarded statement is null (detail 1), yet the delay expression is still
// reachable. A ref-obj operand ("#dly") stands in for the delay here.
TEST_F(DelayControl, IntraAssignmentDelayStillReachesItsDelayExpression) {
  VpiObject delay_expr;
  delay_expr.type = vpiRefObj;  // e.g. the "dly" in "x = #dly y;"

  VpiObject assignment;
  assignment.type = vpiAssignment;

  VpiObject on_assignment;
  on_assignment.type = vpiDelayControl;
  on_assignment.parent = &assignment;
  on_assignment.children = {&delay_expr};

  // Detail 1: no guarded statement for the assignment-associated delay control.
  EXPECT_EQ(vpi_handle(vpiStmt, &on_assignment), nullptr);
  // ... but the vpiDelay edge is unaffected by that carve-out.
  EXPECT_EQ(vpi_handle(vpiDelay, &on_assignment), &delay_expr);
}

// vpiDelay edge cases: a null handle and a delay control with no expression
// child both report no delay expression.
TEST_F(DelayControl, NullAndDelaylessControlsReportNoDelayExpression) {
  EXPECT_EQ(VpiDelayControlDelayExpr(nullptr), nullptr);

  VpiObject only_stmt;
  only_stmt.type = vpiDelayControl;
  VpiObject guarded;
  guarded.type = vpiStmt;
  only_stmt.children = {&guarded};
  EXPECT_EQ(VpiDelayControlDelayExpr(&only_stmt), nullptr);
}

// vpiDelay operand form: a computed delay ("#(a+b)") reaches its delay
// expression just as a bare-constant delay does. The operand is an operation
// object rather than a constant, so this covers the second admitted delay-
// expression kind (the multiple/computed-delay form of §37.3.4) alongside the
// bare-constant and reference forms exercised elsewhere.
TEST_F(DelayControl, ComputedDelayExpressionReachedThroughVpiDelay) {
  VpiObject delay_expr;
  delay_expr.type = vpiOperation;  // e.g. the "a+b" in "#(a+b) stmt;"

  VpiObject delay_control;
  delay_control.type = vpiDelayControl;
  delay_control.children = {&delay_expr};

  EXPECT_EQ(vpi_handle(vpiDelay, &delay_control), &delay_expr);
  EXPECT_EQ(VpiDelayControlDelayExpr(&delay_control), &delay_expr);
}

// vpiStmt negative/discriminator: the guarded-statement scan must not mistake
// the delay operand for the guarded statement. A delay control that carries
// only a delay expression (no statement child) reports a null statement,
// proving the vpiStmt edge selects on the statement kind rather than returning
// the first child. Mirror of the skip the vpiDelay scan performs on the
// statement child.
TEST_F(DelayControl, StatementScanSkipsDelayExpressionChild) {
  VpiObject delay_expr;
  delay_expr.type = vpiConstant;

  VpiObject delay_control;
  delay_control.type = vpiDelayControl;
  delay_control.children = {&delay_expr};

  EXPECT_EQ(vpi_handle(vpiStmt, &delay_control), nullptr);
  EXPECT_EQ(VpiDelayControlStmt(&delay_control), nullptr);
}

}  // namespace
}  // namespace delta
