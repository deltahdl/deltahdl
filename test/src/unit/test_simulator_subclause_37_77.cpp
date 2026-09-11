#include <gtest/gtest.h>

#include "simulator/sv_vpi_user.h"
#include "simulator/vpi.h"

namespace delta {
namespace {

// §37.77 Disables: the object model diagram draws a class definition, bold
// italic letters in a dotted enclosure named "disables", holding two statements
// - a disable statement and a disable fork statement - and draws a single
// labeled edge, vpiExpr, from the disable statement alone to the named scope it
// terminates: a task, a function, a named begin block, or a named fork block.
// The clause carries no BNF, no numbered Details, and no 'shall' sentences;
// that class and that edge are its entire content. The edge needs dedicated
// production code because the scope at its far end is not an expression - its
// own type is a scope kind, not the vpiExpr relation tag - so the generic
// vpiExpr traversal in vpi_handle cannot find it. The disable fork statement
// terminates the calling process's children and names no scope, so it draws no
// such edge.
//
// §37.4.1 makes the class a grouping of both kinds, and §37.60 draws it inside
// `atomic stmt` as a reference, so both are atomic statements and both are
// among the kinds every relation the model draws to the dotted `stmt`
// enclosure reaches. Only the disable was named there, as though vpiDisable
// were the name of the pair rather than the kind of one of them, so a disable
// fork was no statement at all and the body of no loop, branch or block could
// be one. These tests observe both through the public vpi_handle dispatch.

// The fixture installs a context so the public vpi_handle entry point runs its
// real dispatch over the test objects.
class Disables : public ::testing::Test {
 protected:
  void SetUp() override { SetGlobalVpiContext(&ctx_); }
  void TearDown() override { SetGlobalVpiContext(nullptr); }
  VpiContext ctx_;
};

// vpiExpr edge, task target: a disable statement reaches the task it disables
// through the public vpi_handle(vpiExpr, ...) dispatch.
TEST_F(Disables, DisableReachesTaskTargetThroughVpiExpr) {
  VpiObject task;
  task.type = vpiTask;

  VpiObject disable;
  disable.type = vpiDisable;
  disable.children = {&task};

  EXPECT_EQ(vpi_handle(vpiExpr, &disable), &task);
}

// vpiExpr edge, function target: the same edge reaches a disabled function.
TEST_F(Disables, DisableReachesFunctionTargetThroughVpiExpr) {
  VpiObject function;
  function.type = vpiFunction;

  VpiObject disable;
  disable.type = vpiDisable;
  disable.children = {&function};

  EXPECT_EQ(vpi_handle(vpiExpr, &disable), &function);
}

// vpiExpr edge, named begin target: the edge reaches a disabled named begin
// block, observed directly as the sole operand (the kind-directed selection
// among several children is covered separately below).
TEST_F(Disables, DisableReachesNamedBeginTargetThroughVpiExpr) {
  VpiObject named_begin;
  named_begin.type = vpiNamedBegin;

  VpiObject disable;
  disable.type = vpiDisable;
  disable.children = {&named_begin};

  EXPECT_EQ(vpi_handle(vpiExpr, &disable), &named_begin);
}

// vpiExpr edge, named fork target: the edge reaches a disabled named fork
// block, the fourth and last target kind the diagram groups.
TEST_F(Disables, DisableReachesNamedForkTargetThroughVpiExpr) {
  VpiObject named_fork;
  named_fork.type = vpiNamedFork;

  VpiObject disable;
  disable.type = vpiDisable;
  disable.children = {&named_fork};

  EXPECT_EQ(vpi_handle(vpiExpr, &disable), &named_fork);
}

// The edge is target-kind-directed: when the disable object also carries an
// incidental child that is not a disable target, vpiExpr skips it and returns
// the named scope rather than the first child.
TEST_F(Disables, DisableTargetFoundAmongOtherChildren) {
  VpiObject other;
  other.type = vpiOperation;  // not a disable-target scope, listed first

  VpiObject named_begin;
  named_begin.type = vpiNamedBegin;

  VpiObject disable;
  disable.type = vpiDisable;
  disable.children = {&other, &named_begin};

  EXPECT_EQ(vpi_handle(vpiExpr, &disable), &named_begin);
}

// The edge reports no scope when the disable object has no disable-target
// child: the lookup finds nothing to return.
TEST_F(Disables, DisableWithoutTargetReportsNull) {
  VpiObject disable;
  disable.type = vpiDisable;

  EXPECT_EQ(vpi_handle(vpiExpr, &disable), nullptr);
}

// The vpiExpr relation belongs to the plain disable statement only. A disable
// fork terminates the active process's children and names no scope, so it draws
// no vpiExpr edge: even with a scope child attached, the dispatch reports null
// rather than treating that child as a disable target.
TEST_F(Disables, DisableForkHasNoVpiExprTarget) {
  VpiObject named_fork;
  named_fork.type = vpiNamedFork;

  VpiObject disable_fork;
  disable_fork.type = vpiDisableFork;
  disable_fork.children = {&named_fork};

  EXPECT_EQ(vpi_handle(vpiExpr, &disable_fork), nullptr);
}

// The class: the predicate admits the two kinds the diagram draws inside the
// `disables` enclosure and rejects statements of other kinds, including the
// scopes a disable names, which are drawn at the far end of its edge rather
// than in the class.
TEST_F(Disables, VpiIsDisableTypeAdmitsBothKindsAndRejectsOthers) {
  EXPECT_TRUE(VpiIsDisableType(vpiDisable));
  EXPECT_TRUE(VpiIsDisableType(vpiDisableFork));
  EXPECT_FALSE(VpiIsDisableType(vpiNamedFork));
  EXPECT_FALSE(VpiIsDisableType(vpiWaitFork));
  EXPECT_FALSE(VpiIsDisableType(vpiNullStmt));
}

// §37.60 draws the class inside `atomic stmt`, so both kinds are atomic
// statements. A disable fork was not, which put it outside the `stmt` class
// §37.4.1 has every statement relation reach.
TEST_F(Disables, BothKindsAreAtomicStatements) {
  EXPECT_TRUE(VpiIsAtomicStmtType(vpiDisable));
  EXPECT_TRUE(VpiIsAtomicStmtType(vpiDisableFork));
}

// The consequence, observed through a relation: a statement of either kind is
// reached as the body of a loop, which is one of the untagged arrows the model
// draws to `stmt`. "forever disable fork;" is the case the class reference
// decides.
TEST_F(Disables, EitherKindIsReachedAsTheBodyOfALoop) {
  for (int disable_kind : {vpiDisable, vpiDisableFork}) {
    VpiObject body;
    body.type = disable_kind;

    VpiObject forever_stmt;
    forever_stmt.type = vpiForever;
    forever_stmt.children = {&body};

    EXPECT_EQ(vpi_handle(vpiStmt, &forever_stmt), &body)
        << "disable kind " << disable_kind;
  }
}

}  // namespace
}  // namespace delta
