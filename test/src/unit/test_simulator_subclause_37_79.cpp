#include <gtest/gtest.h>

#include "simulator/sv_vpi_user.h"
#include "simulator/vpi.h"

namespace delta {
namespace {

// §37.79 Assign statement, deassign, force, release: the object model diagram
// for the procedural continuous assignment family. The clause carries no BNF,
// no numbered Details, and no 'shall' sentences - it is the diagram alone. The
// diagram draws two dotted enclosures with no name, which §37.4.1 makes
// unnamed classes: groupings that "shall not be referenced as a group
// elsewhere", so what each says is that its members draw the same edges and
// nothing names the pair. The first holds a force and an assign statement and
// carries two single arrows, vpiRhs and vpiLhs, each to an expr; the second
// holds a deassign and a release and carries vpiLhs alone, those two naming a
// target and supplying no value.
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

// Both edges reach whatever expression kind the target or the value is written
// as. §37.59's `expr` class groups the operations, constants and calls, and
// through the `simple expr` class §37.58 nests inside it, the references,
// parameters and selects as well - a forced target is written as a reference or
// a select, and a forced value as any of them.
TEST_F(AssignDeassignForceRelease, EachExpressionKindIsReachedByBothEdges) {
  for (int expr_kind : {vpiOperation, vpiConstant, vpiRefObj, vpiFuncCall,
                        vpiParameter, vpiBitSelect, vpiPartSelect}) {
    VpiObject target;
    target.type = expr_kind;
    VpiObject value;
    value.type = expr_kind;

    VpiObject force;
    force.type = vpiForce;
    force.lhs = &target;
    force.rhs = &value;

    EXPECT_EQ(vpi_handle(vpiLhs, &force), &target) << "kind " << expr_kind;
    EXPECT_EQ(vpi_handle(vpiRhs, &force), &value) << "kind " << expr_kind;
  }
}

// Each of the four kinds claims the edges its class draws: a statement with no
// expression attached reports none, and an expression among its children is not
// taken for one, the edges being held as the statement's own rather than found
// by a walk over what it contains.
TEST_F(AssignDeassignForceRelease, EachKindReportsNoExpressionWhenNoneIsSet) {
  VpiObject stray;
  stray.type = vpiRefObj;  // an expression child, attached to neither edge

  for (int stmt_kind : {vpiAssignStmt, vpiForce, vpiDeassign, vpiRelease}) {
    VpiObject stmt;
    stmt.type = stmt_kind;
    stmt.children = {&stray};

    EXPECT_EQ(vpi_handle(vpiLhs, &stmt), nullptr) << "kind " << stmt_kind;
  }

  // The two that do draw vpiRhs report none when no value is attached either.
  for (int stmt_kind : {vpiAssignStmt, vpiForce}) {
    VpiObject stmt;
    stmt.type = stmt_kind;
    stmt.children = {&stray};

    EXPECT_EQ(vpi_handle(vpiRhs, &stmt), nullptr) << "kind " << stmt_kind;
  }
}

}  // namespace
}  // namespace delta
