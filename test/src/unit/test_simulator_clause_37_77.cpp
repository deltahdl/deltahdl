#include <gtest/gtest.h>

#include "simulator/sv_vpi_user.h"
#include "simulator/vpi.h"

namespace delta {
namespace {

// §37.77 Disables: the object model diagram groups two statements under the
// abstract "disables" label - a disable statement and a disable fork statement -
// and draws a single labeled edge, vpiExpr, from the disable statement to the
// named scope it terminates: a task, a function, a named begin block, or a named
// fork block. The clause carries no BNF, no numbered Details, and no 'shall'
// sentences; that vpiExpr edge and its four target kinds are its entire content.
// The edge needs dedicated production code because the scope at its far end is not
// an expression - its own type is a scope kind, not the vpiExpr relation tag - so
// the generic vpiExpr traversal in VpiHandleC cannot find it. The disable fork
// statement names no scope and so draws no such edge. These tests observe that
// production path applying the rule through the public vpi_handle dispatch.

// The fixture installs a context so the public VpiHandleC entry point runs its
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

  EXPECT_EQ(VpiHandleC(vpiExpr, &disable), &task);
}

// vpiExpr edge, function target: the same edge reaches a disabled function.
TEST_F(Disables, DisableReachesFunctionTargetThroughVpiExpr) {
  VpiObject function;
  function.type = vpiFunction;

  VpiObject disable;
  disable.type = vpiDisable;
  disable.children = {&function};

  EXPECT_EQ(VpiHandleC(vpiExpr, &disable), &function);
}

// vpiExpr edge, named begin target: the edge reaches a disabled named begin
// block, observed directly as the sole operand (the kind-directed selection among
// several children is covered separately below).
TEST_F(Disables, DisableReachesNamedBeginTargetThroughVpiExpr) {
  VpiObject named_begin;
  named_begin.type = vpiNamedBegin;

  VpiObject disable;
  disable.type = vpiDisable;
  disable.children = {&named_begin};

  EXPECT_EQ(VpiHandleC(vpiExpr, &disable), &named_begin);
}

// vpiExpr edge, named fork target: the edge reaches a disabled named fork block,
// the fourth and last target kind the diagram groups.
TEST_F(Disables, DisableReachesNamedForkTargetThroughVpiExpr) {
  VpiObject named_fork;
  named_fork.type = vpiNamedFork;

  VpiObject disable;
  disable.type = vpiDisable;
  disable.children = {&named_fork};

  EXPECT_EQ(VpiHandleC(vpiExpr, &disable), &named_fork);
}

// The edge is target-kind-directed: when the disable object also carries an
// incidental child that is not a disable target, vpiExpr skips it and returns the
// named scope rather than the first child.
TEST_F(Disables, DisableTargetFoundAmongOtherChildren) {
  VpiObject other;
  other.type = vpiOperation;  // not a disable-target scope, listed first

  VpiObject named_begin;
  named_begin.type = vpiNamedBegin;

  VpiObject disable;
  disable.type = vpiDisable;
  disable.children = {&other, &named_begin};

  EXPECT_EQ(VpiHandleC(vpiExpr, &disable), &named_begin);
}

// The edge reports no scope when the disable object has no disable-target child:
// the lookup finds nothing to return.
TEST_F(Disables, DisableWithoutTargetReportsNull) {
  VpiObject disable;
  disable.type = vpiDisable;

  EXPECT_EQ(VpiHandleC(vpiExpr, &disable), nullptr);
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

  EXPECT_EQ(VpiHandleC(vpiExpr, &disable_fork), nullptr);
}

}  // namespace
}  // namespace delta
