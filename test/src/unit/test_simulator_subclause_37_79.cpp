#include <gtest/gtest.h>

#include <vector>

#include "fixture_vpi_run.h"
#include "simulator/sv_vpi_user.h"
#include "simulator/vpi_context.h"
#include "simulator/vpi_globals.h"
#include "simulator/vpi_object.h"
#include "simulator/vpi_user.h"

namespace delta {
namespace {

class AssignDeassignForceRelease : public ::testing::Test {
 protected:
  void SetUp() override { SetGlobalVpiContext(&ctx_); }
  void TearDown() override { SetGlobalVpiContext(nullptr); }
  VpiContext ctx_;
};

TEST_F(AssignDeassignForceRelease, AssignStatementReachesLhsTarget) {
  VpiObject target;
  target.type = vpiRefObj;

  VpiObject assign_stmt;
  assign_stmt.type = vpiAssignStmt;
  assign_stmt.lhs = &target;

  EXPECT_EQ(VpiObjectOf(vpi_handle(vpiLhs, VpiHandleOf(&assign_stmt))),
            &target);
}

TEST_F(AssignDeassignForceRelease, AssignStatementReachesRhsValue) {
  VpiObject value;
  value.type = vpiOperation;

  VpiObject assign_stmt;
  assign_stmt.type = vpiAssignStmt;
  assign_stmt.rhs = &value;

  EXPECT_EQ(VpiObjectOf(vpi_handle(vpiRhs, VpiHandleOf(&assign_stmt))), &value);
}

TEST_F(AssignDeassignForceRelease, ForceReachesRhsValueDistinctFromLhs) {
  VpiObject target;
  target.type = vpiRefObj;
  VpiObject value;
  value.type = vpiOperation;

  VpiObject force;
  force.type = vpiForce;
  force.lhs = &target;
  force.rhs = &value;

  EXPECT_EQ(VpiObjectOf(vpi_handle(vpiRhs, VpiHandleOf(&force))), &value);
  EXPECT_EQ(VpiObjectOf(vpi_handle(vpiLhs, VpiHandleOf(&force))), &target);
}

TEST_F(AssignDeassignForceRelease, DeassignReachesLhsTarget) {
  VpiObject target;
  target.type = vpiRefObj;

  VpiObject deassign;
  deassign.type = vpiDeassign;
  deassign.lhs = &target;

  EXPECT_EQ(VpiObjectOf(vpi_handle(vpiLhs, VpiHandleOf(&deassign))), &target);
}

TEST_F(AssignDeassignForceRelease, ReleaseReachesLhsTarget) {
  VpiObject target;
  target.type = vpiRefObj;

  VpiObject release;
  release.type = vpiRelease;
  release.lhs = &target;

  EXPECT_EQ(VpiObjectOf(vpi_handle(vpiLhs, VpiHandleOf(&release))), &target);
}

TEST_F(AssignDeassignForceRelease, DeassignAndReleaseDrawNoRhsEdge) {
  VpiObject value;
  value.type = vpiOperation;

  VpiObject deassign;
  deassign.type = vpiDeassign;
  deassign.rhs = &value;

  VpiObject release;
  release.type = vpiRelease;
  release.rhs = &value;

  EXPECT_EQ(vpi_handle(vpiRhs, VpiHandleOf(&deassign)), nullptr);
  EXPECT_EQ(vpi_handle(vpiRhs, VpiHandleOf(&release)), nullptr);
}

TEST_F(AssignDeassignForceRelease, LhsRelationIsScopedToTheAssignmentFamily) {
  VpiObject target;
  target.type = vpiRefObj;

  VpiObject not_in_family;
  not_in_family.type = vpiBegin;
  not_in_family.lhs = &target;

  EXPECT_EQ(vpi_handle(vpiLhs, VpiHandleOf(&not_in_family)), nullptr);
}

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

    EXPECT_EQ(VpiObjectOf(vpi_handle(vpiLhs, VpiHandleOf(&force))), &target)
        << "kind " << expr_kind;
    EXPECT_EQ(VpiObjectOf(vpi_handle(vpiRhs, VpiHandleOf(&force))), &value)
        << "kind " << expr_kind;
  }
}

TEST_F(AssignDeassignForceRelease, EachKindReportsNoExpressionWhenNoneIsSet) {
  VpiObject stray;
  stray.type = vpiRefObj;

  for (int stmt_kind : {vpiAssignStmt, vpiForce, vpiDeassign, vpiRelease}) {
    VpiObject stmt;
    stmt.type = stmt_kind;
    stmt.children = {&stray};

    EXPECT_EQ(vpi_handle(vpiLhs, VpiHandleOf(&stmt)), nullptr)
        << "kind " << stmt_kind;
  }

  for (int stmt_kind : {vpiAssignStmt, vpiForce}) {
    VpiObject stmt;
    stmt.type = stmt_kind;
    stmt.children = {&stray};

    EXPECT_EQ(vpi_handle(vpiRhs, VpiHandleOf(&stmt)), nullptr)
        << "kind " << stmt_kind;
  }
}

class ProceduralContinuousAssignmentsOfARun : public VpiDesignRun {};

TEST_F(ProceduralContinuousAssignmentsOfARun, EachIsAnObjectOfTheRun) {
  Run("module top; logic r; wire w;\n"
      "  initial begin assign r = 1; deassign r; force w = 1; release w; end\n"
      "endmodule\n");
  vpiHandle procs = vpi_iterate(vpiProcess, By("top"));
  ASSERT_NE(procs, nullptr);
  vpiHandle block = vpi_handle(vpiStmt, vpi_scan(procs));
  ASSERT_NE(block, nullptr);
  EXPECT_EQ(
      KindsOf(vpiStmt, block),
      (std::vector<int>{vpiAssignStmt, vpiDeassign, vpiForce, vpiRelease}));
  vpiHandle it = vpi_iterate(vpiStmt, block);
  ASSERT_NE(it, nullptr);
  vpiHandle assign = vpi_scan(it);
  vpiHandle deassign = vpi_scan(it);
  vpiHandle force = vpi_scan(it);
  vpiHandle release = vpi_scan(it);
  EXPECT_EQ(VpiObjectOf(vpi_handle(vpiLhs, assign)), VpiObjectOf(By("top.r")));
  EXPECT_EQ(vpi_get(vpiType, vpi_handle(vpiRhs, assign)), vpiConstant);
  EXPECT_EQ(VpiObjectOf(vpi_handle(vpiLhs, deassign)),
            VpiObjectOf(By("top.r")));
  EXPECT_EQ(vpi_handle(vpiRhs, deassign), nullptr);
  EXPECT_EQ(VpiObjectOf(vpi_handle(vpiLhs, force)), VpiObjectOf(By("top.w")));
  EXPECT_EQ(vpi_get(vpiType, vpi_handle(vpiRhs, force)), vpiConstant);
  EXPECT_EQ(VpiObjectOf(vpi_handle(vpiLhs, release)), VpiObjectOf(By("top.w")));
  EXPECT_EQ(vpi_handle(vpiRhs, release), nullptr);
}

}  // namespace
}  // namespace delta
