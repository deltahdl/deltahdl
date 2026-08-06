#include <gtest/gtest.h>

#include "simulator/sv_vpi_user.h"
#include "simulator/vpi.h"

namespace delta {
namespace {

// §37.79 Assign statement, deassign, force, release: the object model diagram
// for the procedural continuous assignment family. The clause carries no BNF,
// no numbered Details, and no 'shall' sentences - it is the diagram alone. The
// diagram groups the four statement kinds into two pairs and draws expression
// edges from them: an assign statement and a force each reach a target through
// vpiLhs and a value through vpiRhs; a deassign and a release each reach a
// target through vpiLhs only (they name a target but supply no value).
//
// Each edge needs dedicated production code because both sides are expression
// kinds (an operation, a reference, a constant, ...), not the vpiLhs / vpiRhs
// relation tags, so the generic child walk in vpi_handle - which matches by
// exact relation tag - cannot find them; they are held as designated pointers.
// These tests observe the production path applying the rule through the public
// vpi_handle dispatch.

// The fixture installs a context so the public vpi_handle entry point runs its
// real dispatch over the test objects.
class AssignDeassignForceRelease : public ::testing::Test {
 protected:
  void SetUp() override { SetGlobalVpiContext(&ctx_); }
  void TearDown() override { SetGlobalVpiContext(nullptr); }
  VpiContext ctx_;
};

// Lhs edge of an assign statement (vpiLhs -> expr): the target the procedural
// continuous assignment drives.
TEST_F(AssignDeassignForceRelease, AssignStatementReachesLhsTarget) {
  VpiObject target;
  target.type = vpiRefObj;

  VpiObject assign_stmt;
  assign_stmt.type = vpiAssignStmt;
  assign_stmt.lhs = &target;

  EXPECT_EQ(vpi_handle(vpiLhs, &assign_stmt), &target);
}

// Rhs edge of an assign statement (vpiRhs -> expr): the value driven onto the
// target.
TEST_F(AssignDeassignForceRelease, AssignStatementReachesRhsValue) {
  VpiObject value;
  value.type = vpiOperation;

  VpiObject assign_stmt;
  assign_stmt.type = vpiAssignStmt;
  assign_stmt.rhs = &value;

  EXPECT_EQ(vpi_handle(vpiRhs, &assign_stmt), &value);
}

// Lhs and rhs edges of a force (vpiLhs/vpiRhs -> expr): the target the force
// overrides and the value forced onto it. The two relations are distinct
// designated pointers, so the dispatch returns the rhs expression for vpiRhs
// and the lhs target for vpiLhs - the force's two diagram edges in one
// observation.
TEST_F(AssignDeassignForceRelease, ForceReachesRhsValueDistinctFromLhs) {
  VpiObject target;
  target.type = vpiRefObj;
  VpiObject value;
  value.type = vpiOperation;

  VpiObject force;
  force.type = vpiForce;
  force.lhs = &target;
  force.rhs = &value;

  EXPECT_EQ(vpi_handle(vpiRhs, &force), &value);
  EXPECT_EQ(vpi_handle(vpiLhs, &force), &target);
}

// Lhs edge of a deassign (vpiLhs -> expr): the target whose procedural
// continuous assignment is removed.
TEST_F(AssignDeassignForceRelease, DeassignReachesLhsTarget) {
  VpiObject target;
  target.type = vpiRefObj;

  VpiObject deassign;
  deassign.type = vpiDeassign;
  deassign.lhs = &target;

  EXPECT_EQ(vpi_handle(vpiLhs, &deassign), &target);
}

// Lhs edge of a release (vpiLhs -> expr): the target whose force is removed.
TEST_F(AssignDeassignForceRelease, ReleaseReachesLhsTarget) {
  VpiObject target;
  target.type = vpiRefObj;

  VpiObject release;
  release.type = vpiRelease;
  release.lhs = &target;

  EXPECT_EQ(vpi_handle(vpiLhs, &release), &target);
}

// The diagram draws no vpiRhs edge from a deassign or a release: they name a
// target but supply no value. The rhs gate is scoped to the assign statement
// and force, so a deassign falls through to the generic walk, which matches by
// exact relation tag and reports null even though an rhs pointer happens to be
// set.
TEST_F(AssignDeassignForceRelease, DeassignAndReleaseDrawNoRhsEdge) {
  VpiObject value;
  value.type = vpiOperation;

  VpiObject deassign;
  deassign.type = vpiDeassign;
  deassign.rhs = &value;

  VpiObject release;
  release.type = vpiRelease;
  release.rhs = &value;

  EXPECT_EQ(vpi_handle(vpiRhs, &deassign), nullptr);
  EXPECT_EQ(vpi_handle(vpiRhs, &release), nullptr);
}

// Lhs gating: the lhs relation is scoped to the four procedural continuous
// assignment kinds, so it does not disturb the vpiLhs edge other objects draw.
// A non-family object is left to the generic traversal, which matches by exact
// relation tag and so does not surface a designated lhs pointer.
TEST_F(AssignDeassignForceRelease, LhsRelationIsScopedToTheAssignmentFamily) {
  VpiObject target;
  target.type = vpiRefObj;

  VpiObject not_in_family;
  not_in_family.type = vpiBegin;  // not an assign/force/deassign/release
  not_in_family.lhs = &target;

  EXPECT_EQ(vpi_handle(vpiLhs, &not_in_family), nullptr);
}

}  // namespace
}  // namespace delta
