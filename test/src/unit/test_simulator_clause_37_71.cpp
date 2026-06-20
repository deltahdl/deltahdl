#include <gtest/gtest.h>

#include "simulator/sv_vpi_user.h"
#include "simulator/vpi.h"

namespace delta {
namespace {

// §37.71 If, if-else: the object model diagram groups a plain if statement and
// an if-else statement. Each draws a vpiCondition edge to a controlling
// condition expression and an unlabeled edge to a then-branch body statement
// (the generic vpiStmt relation); the if-else additionally draws a vpiElseStmt
// edge to an else-branch body statement. Both kinds carry an int vpiQualifier
// property (the unique/priority qualifier flags). The clause has no numbered
// Details and no 'shall' sentences. These tests observe the production code
// that serves the diagram's relations and property: the vpiCondition edge
// through the dedicated helper VpiIfConditionExpr (wired into VpiHandleC), the
// then-branch through the generic vpiStmt traversal, the vpiElseStmt edge
// through VpiIfElseStmt (also wired into VpiHandleC), and the vpiQualifier
// property through the public vpi_get dispatch.

// The fixture installs a context so the public VpiHandleC / vpi_get entry
// points run their real dispatch over the test objects.
class IfIfElse : public ::testing::Test {
 protected:
  void SetUp() override { SetGlobalVpiContext(&ctx_); }
  void TearDown() override { SetGlobalVpiContext(nullptr); }
  VpiContext ctx_;
};

// vpiCondition edge: a plain if statement reaches its condition expression
// through the public vpi_handle(vpiCondition, ...) dispatch path.
TEST_F(IfIfElse, IfStatementReachesConditionThroughVpiCondition) {
  VpiObject condition;
  condition.type = vpiOperation;  // an expression kind

  VpiObject then_body;
  then_body.type = vpiStmt;

  VpiObject if_stmt;
  if_stmt.type = vpiIf;
  if_stmt.children = {&condition, &then_body};

  EXPECT_EQ(VpiHandleC(vpiCondition, &if_stmt), &condition);
}

// vpiCondition edge: an if-else statement reaches its condition the same way -
// the grouping serves both conditional kinds.
TEST_F(IfIfElse, IfElseStatementReachesConditionThroughVpiCondition) {
  VpiObject condition;
  condition.type = vpiRefObj;  // another expression kind

  VpiObject then_body;
  then_body.type = vpiStmt;

  VpiObject else_body;
  else_body.type = vpiStmt;

  VpiObject if_else;
  if_else.type = vpiIfElse;
  if_else.children = {&condition, &then_body, &else_body};

  EXPECT_EQ(VpiHandleC(vpiCondition, &if_else), &condition);
}

// vpiCondition edge: the condition is found even when a non-expression child (a
// body statement) precedes it in the child list. The scan skips the body and
// returns the first expression child.
TEST_F(IfIfElse, ConditionFoundWhenItFollowsABodyChild) {
  VpiObject then_body;
  then_body.type = vpiStmt;  // a non-expression child, listed first

  VpiObject condition;
  condition.type = vpiOperation;

  VpiObject if_stmt;
  if_stmt.type = vpiIf;
  if_stmt.children = {&then_body, &condition};

  EXPECT_EQ(VpiHandleC(vpiCondition, &if_stmt), &condition);
}

// vpiCondition edge is scoped to the conditional statements: asking some other
// statement kind for vpiCondition does not pick up an expression child through
// this path. A repeat control (§37.69 draws its own edges) with an expression
// child yields no condition from the if/if-else dispatch.
TEST_F(IfIfElse, VpiConditionIsScopedToConditionalStatements) {
  VpiObject expr;
  expr.type = vpiOperation;

  VpiObject other;
  other.type = vpiRepeatControl;
  other.children = {&expr};

  EXPECT_EQ(VpiHandleC(vpiCondition, &other), nullptr);
}

// vpiCondition edge, no-condition edge case: a conditional statement that
// carries only body statements (no expression child) yields no condition. This
// reaches the dedicated VpiIfConditionExpr scan - distinct from the scoped test
// above, which is rejected at the type gate before the scan runs - and observes
// the scan completing over the children without finding an expression.
TEST_F(IfIfElse, ConditionIsNullWhenNoExpressionChild) {
  VpiObject then_body;
  then_body.type = vpiStmt;

  VpiObject if_stmt;
  if_stmt.type = vpiIf;
  if_stmt.children = {&then_body};

  EXPECT_EQ(VpiHandleC(vpiCondition, &if_stmt), nullptr);
}

// Then-branch edge (the diagram's unlabeled arrow to a statement): an if
// statement reaches its then body through the generic vpiStmt traversal - the
// first body statement child.
TEST_F(IfIfElse, ThenBodyReachedThroughGenericVpiStmt) {
  VpiObject condition;
  condition.type = vpiOperation;

  VpiObject then_body;
  then_body.type = vpiStmt;

  VpiObject else_body;
  else_body.type = vpiStmt;

  VpiObject if_else;
  if_else.type = vpiIfElse;
  if_else.children = {&condition, &then_body, &else_body};

  EXPECT_EQ(VpiHandleC(vpiStmt, &if_else), &then_body);
}

// vpiElseStmt edge: an if-else statement reaches its else-branch body - the
// second body statement child - through the public vpi_handle(vpiElseStmt, ...)
// dispatch, distinct from the then-branch served by the generic traversal.
TEST_F(IfIfElse, IfElseStatementReachesElseBranchThroughVpiElseStmt) {
  VpiObject condition;
  condition.type = vpiOperation;

  VpiObject then_body;
  then_body.type = vpiStmt;

  VpiObject else_body;
  else_body.type = vpiStmt;

  VpiObject if_else;
  if_else.type = vpiIfElse;
  if_else.children = {&condition, &then_body, &else_body};

  EXPECT_EQ(VpiHandleC(vpiElseStmt, &if_else), &else_body);
}

// vpiElseStmt is drawn only from the if-else grouping: a plain if statement
// reports no else branch even when it carries a second body statement child,
// because the relation is gated on the if-else kind.
TEST_F(IfIfElse, PlainIfReportsNoElseStatement) {
  VpiObject condition;
  condition.type = vpiOperation;

  VpiObject then_body;
  then_body.type = vpiStmt;

  VpiObject second_body;
  second_body.type = vpiStmt;

  VpiObject if_stmt;
  if_stmt.type = vpiIf;
  if_stmt.children = {&condition, &then_body, &second_body};

  EXPECT_EQ(VpiHandleC(vpiElseStmt, &if_stmt), nullptr);
}

// vpiElseStmt edge: an if-else statement with only a then branch (a single body
// statement) reports no else branch.
TEST_F(IfIfElse, ElseStatementIsNullWhenNoElseBranch) {
  VpiObject condition;
  condition.type = vpiOperation;

  VpiObject then_body;
  then_body.type = vpiStmt;

  VpiObject if_else;
  if_else.type = vpiIfElse;
  if_else.children = {&condition, &then_body};

  EXPECT_EQ(VpiHandleC(vpiElseStmt, &if_else), nullptr);
}

// Property (-> qualifier int: vpiQualifier): an if or if-else statement reports
// its qualifier flags (a bitwise OR of the unique/priority/etc. qualifiers,
// vpiNoQualifier when none) as an int property through the public vpi_get
// dispatch.
TEST_F(IfIfElse, ConditionalStatementReportsQualifier) {
  VpiObject if_stmt;
  if_stmt.type = vpiIf;
  if_stmt.qualifier = vpiUniqueQualifier;
  EXPECT_EQ(vpi_get(vpiQualifier, &if_stmt), vpiUniqueQualifier);

  VpiObject if_else;
  if_else.type = vpiIfElse;
  if_else.qualifier = vpiPriorityQualifier;
  EXPECT_EQ(vpi_get(vpiQualifier, &if_else), vpiPriorityQualifier);

  // An if statement written with no qualifier reports the "none" sentinel.
  VpiObject plain_if;
  plain_if.type = vpiIf;
  EXPECT_EQ(vpi_get(vpiQualifier, &plain_if), vpiNoQualifier);
}

}  // namespace
}  // namespace delta
