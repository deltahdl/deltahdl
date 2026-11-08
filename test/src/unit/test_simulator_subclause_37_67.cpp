#include <gtest/gtest.h>

#include <vector>

#include "fixture_vpi_run.h"
#include "simulator/sv_vpi_user.h"
#include "simulator/vpi_context.h"
#include "simulator/vpi_globals.h"
#include "simulator/vpi_model_helpers1.h"
#include "simulator/vpi_object.h"
#include "simulator/vpi_user.h"

namespace delta {
namespace {

class Waits : public ::testing::Test {
 protected:
  void SetUp() override { SetGlobalVpiContext(&ctx_); }
  void TearDown() override { SetGlobalVpiContext(nullptr); }
  VpiContext ctx_;
};

TEST_F(Waits, WaitReachesExpressionCondition) {
  VpiObject condition;
  condition.type = vpiOperation;

  VpiObject body;
  body.type = vpiBegin;

  VpiObject wait_stmt;
  wait_stmt.type = vpiWait;
  wait_stmt.children = {&condition, &body};

  EXPECT_EQ(VpiWaitConditionExpr(&wait_stmt), &condition);
  EXPECT_EQ(VpiObjectOf(vpi_handle(vpiCondition, VpiHandleOf(&wait_stmt))),
            &condition);
}

TEST_F(Waits, OrderedWaitReachesSequenceInstanceCondition) {
  VpiObject condition;
  condition.type = vpiSequenceInst;

  VpiObject ordered_wait;
  ordered_wait.type = vpiOrderedWait;
  ordered_wait.children = {&condition};

  EXPECT_EQ(VpiWaitConditionExpr(&ordered_wait), &condition);
  EXPECT_EQ(VpiObjectOf(vpi_handle(vpiCondition, VpiHandleOf(&ordered_wait))),
            &condition);
}

TEST_F(Waits, ConditionFoundAfterPrecedingBodyChild) {
  VpiObject body;
  body.type = vpiBegin;

  VpiObject condition;
  condition.type = vpiRefObj;

  VpiObject wait_stmt;
  wait_stmt.type = vpiWait;
  wait_stmt.children = {&body, &condition};

  EXPECT_EQ(VpiWaitConditionExpr(&wait_stmt), &condition);
}

TEST_F(Waits, ConditionNullWhenAbsentOrHandleNull) {
  EXPECT_EQ(VpiWaitConditionExpr(nullptr), nullptr);

  VpiObject body;
  body.type = vpiBegin;

  VpiObject wait_fork;
  wait_fork.type = vpiWaitFork;
  wait_fork.children = {&body};
  EXPECT_EQ(VpiWaitConditionExpr(&wait_fork), nullptr);
  EXPECT_EQ(vpi_handle(vpiCondition, VpiHandleOf(&wait_fork)), nullptr);
}

TEST_F(Waits, VpiIsWaitTypeAdmitsWaitKindsRejectsOthers) {
  EXPECT_TRUE(VpiIsWaitType(vpiWait));
  EXPECT_TRUE(VpiIsWaitType(vpiOrderedWait));
  EXPECT_TRUE(VpiIsWaitType(vpiWaitFork));
  EXPECT_FALSE(VpiIsWaitType(vpiWhile));
}

TEST_F(Waits, BodyStatementReachedByTheKindTheStmtClassGroups) {
  for (int wait_kind : {vpiWait, vpiOrderedWait, vpiWaitFork}) {
    VpiObject condition;
    condition.type = vpiOperation;

    VpiObject body;
    body.type = vpiBegin;

    VpiObject wait_stmt;
    wait_stmt.type = wait_kind;
    wait_stmt.children = {&condition, &body};

    EXPECT_EQ(VpiObjectOf(vpi_handle(vpiStmt, VpiHandleOf(&wait_stmt))), &body)
        << "wait kind " << wait_kind;
  }
}

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

  EXPECT_EQ(VpiObjectOf(vpi_handle(vpiStmt, VpiHandleOf(&ordered_wait))),
            &body);
  EXPECT_EQ(VpiObjectOf(vpi_handle(vpiElseStmt, VpiHandleOf(&ordered_wait))),
            &else_stmt);
  EXPECT_EQ(VpiOrderedWaitElseStmt(&ordered_wait), &else_stmt);
}

TEST_F(Waits, ElseStatementIsNullWhenTheOrderedWaitHasOnlyABody) {
  VpiObject body;
  body.type = vpiBegin;

  VpiObject ordered_wait;
  ordered_wait.type = vpiOrderedWait;
  ordered_wait.children = {&body};

  EXPECT_EQ(vpi_handle(vpiElseStmt, VpiHandleOf(&ordered_wait)), nullptr);
  EXPECT_EQ(VpiOrderedWaitElseStmt(nullptr), nullptr);

  VpiObject wait_fork;
  wait_fork.type = vpiWaitFork;
  wait_fork.children = {&body};
  EXPECT_EQ(VpiOrderedWaitElseStmt(&wait_fork), nullptr);
}

class WaitsOfARun : public VpiDesignRun {
 protected:
  static std::vector<vpiHandle> BlockStatements() {
    std::vector<vpiHandle> stmts;
    vpiHandle procs = vpi_iterate(vpiProcess, By("top"));
    vpiHandle block = procs ? vpi_handle(vpiStmt, vpi_scan(procs)) : nullptr;
    vpiHandle it = block ? vpi_iterate(vpiStmt, block) : nullptr;
    while (vpiHandle stmt = it ? vpi_scan(it) : nullptr) stmts.push_back(stmt);
    return stmts;
  }
};

TEST_F(WaitsOfARun, AWaitAndAWaitForkAreObjectsOfTheRun) {
  Run("module top; bit c; int a;\n"
      "  initial begin fork #1; join_none wait fork; wait (c) a = 1; end\n"
      "  initial #2 c = 1;\n"
      "endmodule\n");
  const std::vector<vpiHandle> kStmts = BlockStatements();
  ASSERT_EQ(kStmts.size(), 3U);
  EXPECT_EQ(vpi_get(vpiType, kStmts[1]), vpiWaitFork);
  EXPECT_EQ(vpi_handle(vpiCondition, kStmts[1]), nullptr);
  EXPECT_EQ(vpi_get(vpiType, kStmts[2]), vpiWait);
  EXPECT_EQ(VpiObjectOf(vpi_handle(vpiCondition, kStmts[2])),
            VpiObjectOf(By("top.c")));
  vpiHandle guarded = vpi_handle(vpiStmt, kStmts[2]);
  ASSERT_NE(guarded, nullptr);
  EXPECT_EQ(vpi_get(vpiType, guarded), vpiAssignment);
}

TEST_F(WaitsOfARun, AnOrderedWaitReachesBothActions) {
  Run("module top; event a, b; int r;\n"
      "  initial begin wait_order (a, b) r = 1; else r = 2; end\n"
      "endmodule\n");
  const std::vector<vpiHandle> kStmts = BlockStatements();
  ASSERT_EQ(kStmts.size(), 1U);
  EXPECT_EQ(vpi_get(vpiType, kStmts[0]), vpiOrderedWait);
  vpiHandle action = vpi_handle(vpiStmt, kStmts[0]);
  vpiHandle otherwise = vpi_handle(vpiElseStmt, kStmts[0]);
  ASSERT_NE(action, nullptr);
  ASSERT_NE(otherwise, nullptr);
  EXPECT_NE(VpiObjectOf(action), VpiObjectOf(otherwise));
  EXPECT_EQ(vpi_get(vpiType, otherwise), vpiAssignment);
}

TEST_F(WaitsOfARun, AnElseActionAloneIsTheElseStatement) {
  Run("module top; event a, b; int r;\n"
      "  initial begin wait_order (a, b) else r = 2; end\n"
      "endmodule\n");
  const std::vector<vpiHandle> kStmts = BlockStatements();
  ASSERT_EQ(kStmts.size(), 1U);
  EXPECT_EQ(vpi_get(vpiType, kStmts[0]), vpiOrderedWait);
  EXPECT_EQ(vpi_handle(vpiStmt, kStmts[0]), nullptr);
  vpiHandle otherwise = vpi_handle(vpiElseStmt, kStmts[0]);
  ASSERT_NE(otherwise, nullptr);
  EXPECT_EQ(vpi_get(vpiType, otherwise), vpiAssignment);
}

TEST_F(WaitsOfARun, AnOrderedWaitIteratesTheEventsItWaitsOn) {
  Run("module top; event a, b; int r;\n"
      "  initial begin wait_order (b, a) r = 1; else r = 2; end\n"
      "endmodule\n");
  const std::vector<vpiHandle> kStmts = BlockStatements();
  ASSERT_EQ(kStmts.size(), 1U);
  vpiHandle it = vpi_iterate(vpiCondition, kStmts[0]);
  ASSERT_NE(it, nullptr);
  EXPECT_EQ(VpiObjectOf(vpi_scan(it)), VpiObjectOf(By("top.b")));
  EXPECT_EQ(VpiObjectOf(vpi_scan(it)), VpiObjectOf(By("top.a")));
  EXPECT_EQ(vpi_scan(it), nullptr);
  EXPECT_EQ(vpi_iterate(vpiAttribute, kStmts[0]), nullptr);
}

}  // namespace
}  // namespace delta
