#include <gtest/gtest.h>

#include "simulator/sv_vpi_user.h"
#include "simulator/vpi.h"

namespace delta {
namespace {

// §37.67 Waits: the object model diagram groups three wait statements - a wait,
// an ordered wait, and a wait fork - under the abstract "waits" label. It draws
// a vpiCondition edge from the wait and ordered wait to a controlling condition
// that is either an expression or a sequence instance, an unlabeled edge from
// the grouping to a body statement (the vpiStmt relation), and a vpiElseStmt
// edge to an else action statement. The clause carries no numbered Details, no
// BNF, and no 'shall' sentences. These tests observe the production code that
// serves the diagram's relations: the vpiCondition edge through the dedicated
// helper VpiWaitConditionExpr, and the body and else edges through the generic
// traversal.

// The fixture installs a context so the public vpi_handle entry point runs its
// real dispatch over the test objects.
class Waits : public ::testing::Test {
 protected:
  void SetUp() override { SetGlobalVpiContext(&ctx_); }
  void TearDown() override { SetGlobalVpiContext(nullptr); }
  VpiContext ctx_;
};

// vpiCondition edge: a wait statement reaches an expression condition. The
// public vpiCondition dispatch serves the wait through the dedicated helper,
// because the condition's own type is an expression kind rather than the
// vpiCondition relation tag and so the generic child walk cannot find it. Both
// the helper and the public entry point reach the same condition.
TEST_F(Waits, WaitReachesExpressionCondition) {
  VpiObject condition;
  condition.type = vpiOperation;  // an expression kind

  VpiObject body;
  body.type = vpiStmt;

  VpiObject wait_stmt;
  wait_stmt.type = vpiWait;
  wait_stmt.children = {&condition, &body};

  EXPECT_EQ(VpiWaitConditionExpr(&wait_stmt), &condition);
  EXPECT_EQ(vpi_handle(vpiCondition, &wait_stmt), &condition);
}

// vpiCondition edge: an ordered wait reaches a sequence-instance condition.
// This exercises the sequence-instance branch the diagram draws alongside the
// expression branch - the kind a plain expression scan would miss.
TEST_F(Waits, OrderedWaitReachesSequenceInstanceCondition) {
  VpiObject condition;
  condition.type = vpiSequenceInst;

  VpiObject ordered_wait;
  ordered_wait.type = vpiOrderedWait;
  ordered_wait.children = {&condition};

  EXPECT_EQ(VpiWaitConditionExpr(&ordered_wait), &condition);
  EXPECT_EQ(vpi_handle(vpiCondition, &ordered_wait), &condition);
}

// vpiCondition edge: the condition is found even when a non-condition child
// (the body statement) precedes it in the child list. The scan skips the body
// and returns the first expression-or-sequence child.
TEST_F(Waits, ConditionFoundAfterPrecedingBodyChild) {
  VpiObject body;
  body.type =
      vpiStmt;  // neither an expression nor a sequence inst, listed first

  VpiObject condition;
  condition.type = vpiRefObj;  // another expression kind

  VpiObject wait_stmt;
  wait_stmt.type = vpiWait;
  wait_stmt.children = {&body, &condition};

  EXPECT_EQ(VpiWaitConditionExpr(&wait_stmt), &condition);
}

// vpiCondition edge: a null handle and a wait with no condition child both
// report no condition. A wait fork draws no condition edge, so it stands in for
// the no-condition case here.
TEST_F(Waits, ConditionNullWhenAbsentOrHandleNull) {
  EXPECT_EQ(VpiWaitConditionExpr(nullptr), nullptr);

  VpiObject body;
  body.type = vpiStmt;

  VpiObject wait_fork;
  wait_fork.type = vpiWaitFork;
  wait_fork.children = {&body};  // only a body, no condition
  EXPECT_EQ(VpiWaitConditionExpr(&wait_fork), nullptr);
  // The wait-statement gate admits a wait fork, but it draws no condition edge,
  // so the public dispatch reports null rather than mistaking the body for one.
  EXPECT_EQ(vpi_handle(vpiCondition, &wait_fork), nullptr);
}

// The "waits" grouping: the predicate admits the three wait kinds the diagram
// draws and rejects unrelated statement kinds (here a while loop, which belongs
// to the separate §37.66 grouping).
TEST_F(Waits, VpiIsWaitTypeAdmitsWaitKindsRejectsOthers) {
  EXPECT_TRUE(VpiIsWaitType(vpiWait));
  EXPECT_TRUE(VpiIsWaitType(vpiOrderedWait));
  EXPECT_TRUE(VpiIsWaitType(vpiWaitFork));
  EXPECT_FALSE(VpiIsWaitType(vpiWhile));
}

// Body edge (the diagram's unlabeled arrow to a statement): a wait reaches its
// body through the generic vpiStmt traversal.
TEST_F(Waits, BodyStatementReachedThroughGenericVpiStmt) {
  VpiObject condition;
  condition.type = vpiOperation;

  VpiObject body;
  body.type = vpiStmt;

  VpiObject wait_stmt;
  wait_stmt.type = vpiWait;
  wait_stmt.children = {&condition, &body};

  EXPECT_EQ(vpi_handle(vpiStmt, &wait_stmt), &body);
}

// Else edge (the diagram's vpiElseStmt arrow to a statement): a wait fork
// reaches its else action statement through the generic vpiElseStmt traversal,
// since the else child carries the relation tag as its own type.
TEST_F(Waits, ElseStatementReachedThroughGenericVpiElseStmt) {
  VpiObject else_stmt;
  else_stmt.type = vpiElseStmt;

  VpiObject wait_fork;
  wait_fork.type = vpiWaitFork;
  wait_fork.children = {&else_stmt};

  EXPECT_EQ(vpi_handle(vpiElseStmt, &wait_fork), &else_stmt);
}

}  // namespace
}  // namespace delta
