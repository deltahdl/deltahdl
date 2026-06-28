#include <gtest/gtest.h>

#include "simulator/sv_vpi_user.h"
#include "simulator/vpi.h"

namespace delta {
namespace {

// §37.66 While, repeat: the object model diagram groups a while statement and a
// repeat statement, drawing a vpiCondition edge from each to a controlling
// condition expression and an unlabeled edge from each to a body statement (the
// vpiStmt relation). The clause carries no numbered Details and no 'shall'
// sentences. These tests observe the production code that serves the diagram's
// relations: the vpiCondition edge through the dedicated helper
// VpiLoopConditionExpr (wired into vpi_handle), and the body edge through the
// generic vpiStmt traversal.

// The fixture installs a context so the public vpi_handle entry point runs its
// real dispatch over the test objects.
class WhileRepeat : public ::testing::Test {
 protected:
  void SetUp() override { SetGlobalVpiContext(&ctx_); }
  void TearDown() override { SetGlobalVpiContext(nullptr); }
  VpiContext ctx_;
};

// vpiCondition edge: a while statement reaches its condition expression through
// the public vpi_handle(vpiCondition, ...) dispatch path.
TEST_F(WhileRepeat, WhileStatementReachesConditionThroughVpiCondition) {
  VpiObject condition;
  condition.type = vpiOperation;  // an expression kind

  VpiObject body;
  body.type = vpiStmt;

  VpiObject while_stmt;
  while_stmt.type = vpiWhile;
  while_stmt.children = {&condition, &body};

  EXPECT_EQ(vpi_handle(vpiCondition, &while_stmt), &condition);
}

// vpiCondition edge: a repeat statement reaches its condition expression the
// same way - the grouping serves both looping kinds.
TEST_F(WhileRepeat, RepeatStatementReachesConditionThroughVpiCondition) {
  VpiObject condition;
  condition.type = vpiRefObj;  // another expression kind

  VpiObject repeat_stmt;
  repeat_stmt.type = vpiRepeat;
  repeat_stmt.children = {&condition};

  EXPECT_EQ(vpi_handle(vpiCondition, &repeat_stmt), &condition);
}

// vpiCondition edge: the condition is found even when a non-expression child
// (the loop body statement) precedes it in the child list. The scan skips the
// body and returns the first expression child.
TEST_F(WhileRepeat, ConditionFoundWhenItFollowsTheBodyChild) {
  VpiObject body;
  body.type = vpiStmt;  // a non-expression child, listed first

  VpiObject condition;
  condition.type = vpiOperation;

  VpiObject while_stmt;
  while_stmt.type = vpiWhile;
  while_stmt.children = {&body, &condition};

  EXPECT_EQ(vpi_handle(vpiCondition, &while_stmt), &condition);
}

// vpiCondition edge: a null handle and a loop with no expression child both
// report no condition.
TEST_F(WhileRepeat, ConditionIsNullWhenAbsentOrHandleNull) {
  EXPECT_EQ(VpiLoopConditionExpr(nullptr), nullptr);

  VpiObject body;
  body.type = vpiStmt;

  VpiObject bare_loop;
  bare_loop.type = vpiWhile;
  bare_loop.children = {&body};  // only a body, no condition expression
  EXPECT_EQ(VpiLoopConditionExpr(&bare_loop), nullptr);
}

// vpiCondition edge is scoped to the loop statements: asking a non-loop
// statement for vpiCondition does not pick up an expression child through this
// path. The negative control must be a genuinely condition-less statement -- a
// forever loop (§37.70 draws no controlling-condition edge), not a wait (§37.67
// draws its own vpiCondition, served publicly). A forever with an expression
// child yields no condition from the while/repeat dispatch.
TEST_F(WhileRepeat, VpiConditionIsScopedToLoopStatements) {
  VpiObject condition;
  condition.type = vpiOperation;

  VpiObject forever_stmt;
  forever_stmt.type = vpiForever;
  forever_stmt.children = {&condition};

  EXPECT_EQ(vpi_handle(vpiCondition, &forever_stmt), nullptr);
}

// Body edge (the diagram's unlabeled arrow to a statement): a while statement
// reaches its body through the generic vpiStmt traversal.
TEST_F(WhileRepeat, LoopBodyReachedThroughGenericVpiStmt) {
  VpiObject condition;
  condition.type = vpiOperation;

  VpiObject body;
  body.type = vpiStmt;

  VpiObject while_stmt;
  while_stmt.type = vpiWhile;
  while_stmt.children = {&condition, &body};

  EXPECT_EQ(vpi_handle(vpiStmt, &while_stmt), &body);
}

}  // namespace
}  // namespace delta
