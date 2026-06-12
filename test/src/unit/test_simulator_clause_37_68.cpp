#include <gtest/gtest.h>

#include "simulator/sv_vpi_user.h"
#include "simulator/vpi.h"

namespace delta {
namespace {

// §37.68 Delay control: the object model diagram draws a delay control "#" object
// with a vpiDelay relation (to an expression, plus the delay set reached via
// vpi_get_delays(), §38.10) and a vpiStmt edge to a statement. The clause's sole
// numbered Detail (D1) governs that statement edge: when the delay control is
// associated with an assignment, the statement shall always be NULL. These tests
// observe the production code that applies that rule (VpiDelayControlStmt) both
// directly and through the public VpiHandleC(vpiStmt, ...) dispatch path.

// The fixture installs a context so the public VpiHandleC entry point runs its
// real dispatch over the test objects.
class DelayControl : public ::testing::Test {
 protected:
  void SetUp() override { SetGlobalVpiContext(&ctx_); }
  void TearDown() override { SetGlobalVpiContext(nullptr); }
  VpiContext ctx_;
};

// D1: a delay control associated with an assignment - its parent is the
// assignment object (§37.64) - reports a null statement even when a statement
// child is physically attached.
TEST_F(DelayControl, AssignmentAssociatedDelayControlHasNullStatement) {
  VpiObject stmt;
  stmt.type = vpiStmt;

  VpiObject assignment;
  assignment.type = vpiAssignment;

  VpiObject delay_control;
  delay_control.type = vpiDelayControl;
  delay_control.parent = &assignment;
  delay_control.children = {&stmt};

  EXPECT_EQ(VpiDelayControlStmt(&delay_control), nullptr);
}

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

// D1 edge: a null handle and a delay control with no statement child both report
// no statement.
TEST_F(DelayControl, NullAndEmptyDelayControlsReportNoStatement) {
  EXPECT_EQ(VpiDelayControlStmt(nullptr), nullptr);

  VpiObject bare;
  bare.type = vpiDelayControl;
  EXPECT_EQ(VpiDelayControlStmt(&bare), nullptr);
}

// D1 end to end: the rule is applied by the public VpiHandleC(vpiStmt, ...)
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
  EXPECT_EQ(VpiHandleC(vpiStmt, &on_assignment), nullptr);

  VpiObject standalone;
  standalone.type = vpiDelayControl;
  standalone.children = {&guarded};
  EXPECT_EQ(VpiHandleC(vpiStmt, &standalone), &guarded);
}

}  // namespace
}  // namespace delta
