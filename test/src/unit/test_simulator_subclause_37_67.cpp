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
// helper VpiWaitConditionExpr, the body edge through the resolver that reads
// the dotted `stmt` enclosure as §37.4.1 reads it - a class grouping other
// objects, never a kind a statement of a design carries - and the else edge
// through the helper that tells an ordered wait's else action from its body by
// position. Both of those last two were left to the walk that looks for a child
// whose own type is the relation tag, which is a kind no statement has, so
// neither edge reached anything a design could hold.

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
  body.type = vpiBegin;  // a statement kind the `stmt` class groups

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
  body.type = vpiBegin;  // neither an expression nor a sequence inst, first

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
  body.type = vpiBegin;  // a statement kind the `stmt` class groups

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

// Body edge (the diagram's untagged arrow from the `waits` enclosure to
// `stmt`): each of the three wait kinds reaches its body through
// vpi_handle(vpiStmt, ...). The bodies carry the kinds a statement of a design
// carries rather than vpiStmt, which §37.4.1 makes the name of the class the
// enclosure groups and not a kind any object has.
TEST_F(Waits, BodyStatementReachedByTheKindTheStmtClassGroups) {
  for (int wait_kind : {vpiWait, vpiOrderedWait, vpiWaitFork}) {
    VpiObject condition;
    condition.type = vpiOperation;

    VpiObject body;
    body.type = vpiBegin;

    VpiObject wait_stmt;
    wait_stmt.type = wait_kind;
    wait_stmt.children = {&condition, &body};

    EXPECT_EQ(vpi_handle(vpiStmt, &wait_stmt), &body)
        << "wait kind " << wait_kind;
  }
}

// Else edge (the diagram's vpiElseStmt arrow to `stmt`): an ordered wait
// reaches its else action statement. §9.4.4 writes a wait_order's action block
// as "[ statement_or_null ] [ else statement_or_null ]", so the two statements
// are told apart by position: the first is the body vpiStmt reaches and the
// second is the else action. Both carry real statement kinds, the else's own
// type being no more vpiElseStmt than the body's is vpiStmt.
TEST_F(Waits, ElseStatementOfAnOrderedWaitIsTheSecondStatement) {
  VpiObject condition;
  condition.type = vpiOperation;

  VpiObject body;
  body.type = vpiBegin;

  VpiObject else_stmt;
  else_stmt.type = vpiAssignment;

  VpiObject ordered_wait;
  ordered_wait.type = vpiOrderedWait;
  ordered_wait.children = {&condition, &body, &else_stmt};

  EXPECT_EQ(vpi_handle(vpiStmt, &ordered_wait), &body);
  EXPECT_EQ(vpi_handle(vpiElseStmt, &ordered_wait), &else_stmt);
  EXPECT_EQ(VpiOrderedWaitElseStmt(&ordered_wait), &else_stmt);
}

// Else edge: an ordered wait written with a body and no else action reaches no
// else statement, so the one statement it carries is not handed back for both
// edges. A null handle and a kind that draws no else edge report none either.
TEST_F(Waits, ElseStatementIsNullWhenTheOrderedWaitHasOnlyABody) {
  VpiObject body;
  body.type = vpiBegin;

  VpiObject ordered_wait;
  ordered_wait.type = vpiOrderedWait;
  ordered_wait.children = {&body};

  EXPECT_EQ(vpi_handle(vpiElseStmt, &ordered_wait), nullptr);
  EXPECT_EQ(VpiOrderedWaitElseStmt(nullptr), nullptr);

  VpiObject wait_fork;
  wait_fork.type = vpiWaitFork;
  wait_fork.children = {&body};
  EXPECT_EQ(VpiOrderedWaitElseStmt(&wait_fork), nullptr);
}

}  // namespace
}  // namespace delta
