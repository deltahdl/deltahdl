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

class Disables : public ::testing::Test {
 protected:
  void SetUp() override { SetGlobalVpiContext(&ctx_); }
  void TearDown() override { SetGlobalVpiContext(nullptr); }
  VpiContext ctx_;
};

TEST_F(Disables, DisableReachesTaskTargetThroughVpiExpr) {
  VpiObject task;
  task.type = vpiTask;

  VpiObject disable;
  disable.type = vpiDisable;
  disable.children = {&task};

  EXPECT_EQ(VpiObjectOf(vpi_handle(vpiExpr, VpiHandleOf(&disable))), &task);
}

TEST_F(Disables, DisableReachesFunctionTargetThroughVpiExpr) {
  VpiObject function;
  function.type = vpiFunction;

  VpiObject disable;
  disable.type = vpiDisable;
  disable.children = {&function};

  EXPECT_EQ(VpiObjectOf(vpi_handle(vpiExpr, VpiHandleOf(&disable))), &function);
}

TEST_F(Disables, DisableReachesNamedBeginTargetThroughVpiExpr) {
  VpiObject named_begin;
  named_begin.type = vpiNamedBegin;

  VpiObject disable;
  disable.type = vpiDisable;
  disable.children = {&named_begin};

  EXPECT_EQ(VpiObjectOf(vpi_handle(vpiExpr, VpiHandleOf(&disable))),
            &named_begin);
}

TEST_F(Disables, DisableReachesNamedForkTargetThroughVpiExpr) {
  VpiObject named_fork;
  named_fork.type = vpiNamedFork;

  VpiObject disable;
  disable.type = vpiDisable;
  disable.children = {&named_fork};

  EXPECT_EQ(VpiObjectOf(vpi_handle(vpiExpr, VpiHandleOf(&disable))),
            &named_fork);
}

TEST_F(Disables, DisableTargetFoundAmongOtherChildren) {
  VpiObject other;
  other.type = vpiOperation;

  VpiObject named_begin;
  named_begin.type = vpiNamedBegin;

  VpiObject disable;
  disable.type = vpiDisable;
  disable.children = {&other, &named_begin};

  EXPECT_EQ(VpiObjectOf(vpi_handle(vpiExpr, VpiHandleOf(&disable))),
            &named_begin);
}

TEST_F(Disables, DisableWithoutTargetReportsNull) {
  VpiObject disable;
  disable.type = vpiDisable;

  EXPECT_EQ(vpi_handle(vpiExpr, VpiHandleOf(&disable)), nullptr);
}

TEST_F(Disables, DisableForkHasNoVpiExprTarget) {
  VpiObject named_fork;
  named_fork.type = vpiNamedFork;

  VpiObject disable_fork;
  disable_fork.type = vpiDisableFork;
  disable_fork.children = {&named_fork};

  EXPECT_EQ(vpi_handle(vpiExpr, VpiHandleOf(&disable_fork)), nullptr);
}

TEST_F(Disables, VpiIsDisableTypeAdmitsBothKindsAndRejectsOthers) {
  EXPECT_TRUE(VpiIsDisableType(vpiDisable));
  EXPECT_TRUE(VpiIsDisableType(vpiDisableFork));
  EXPECT_FALSE(VpiIsDisableType(vpiNamedFork));
  EXPECT_FALSE(VpiIsDisableType(vpiWaitFork));
  EXPECT_FALSE(VpiIsDisableType(vpiNullStmt));
}

TEST_F(Disables, BothKindsAreAtomicStatements) {
  EXPECT_TRUE(VpiIsAtomicStmtType(vpiDisable));
  EXPECT_TRUE(VpiIsAtomicStmtType(vpiDisableFork));
}

TEST_F(Disables, EitherKindIsReachedAsTheBodyOfALoop) {
  for (int disable_kind : {vpiDisable, vpiDisableFork}) {
    VpiObject body;
    body.type = disable_kind;

    VpiObject forever_stmt;
    forever_stmt.type = vpiForever;
    forever_stmt.children = {&body};

    EXPECT_EQ(VpiObjectOf(vpi_handle(vpiStmt, VpiHandleOf(&forever_stmt))),
              &body)
        << "disable kind " << disable_kind;
  }
}

class DisablesOfARun : public VpiDesignRun {
 protected:
  static vpiHandle NthBody(int n) {
    vpiHandle it = vpi_iterate(vpiProcess, By("top"));
    vpiHandle proc = nullptr;
    for (int i = 0; i <= n && it != nullptr; ++i) proc = vpi_scan(it);
    return proc == nullptr ? nullptr : vpi_handle(vpiStmt, proc);
  }
};

TEST_F(DisablesOfARun, ABlockDisablingItselfIsReached) {
  Run("module top; initial begin : blk disable blk; end endmodule\n");
  vpiHandle blk = By("top.blk");
  ASSERT_NE(blk, nullptr);
  vpiHandle it = vpi_iterate(vpiStmt, blk);
  ASSERT_NE(it, nullptr);
  vpiHandle disable = vpi_scan(it);
  ASSERT_NE(disable, nullptr);
  EXPECT_EQ(vpi_get(vpiType, disable), vpiDisable);
  EXPECT_EQ(VpiObjectOf(vpi_handle(vpiExpr, disable)), VpiObjectOf(blk));
}

TEST_F(DisablesOfARun, ADisableOfATaskReachesTheTask) {
  Run("module top; task t; #5; endtask\n"
      "  initial t;\n"
      "  initial #1 disable t;\n"
      "endmodule\n");
  vpiHandle delay = NthBody(1);
  ASSERT_NE(delay, nullptr);
  vpiHandle disable = vpi_handle(vpiStmt, delay);
  ASSERT_NE(disable, nullptr);
  EXPECT_EQ(vpi_get(vpiType, disable), vpiDisable);
  vpiHandle task = vpi_handle(vpiExpr, disable);
  ASSERT_NE(task, nullptr);
  EXPECT_EQ(vpi_get(vpiType, task), vpiTask);
  EXPECT_STREQ(vpi_get_str(vpiName, task), "t");
}

TEST_F(DisablesOfARun, AHierarchicalNameReachesTheBlockItNames) {
  Run("module top; initial begin : outer\n"
      "  begin : inner #1; end disable outer.inner;\n"
      "end endmodule\n");
  vpiHandle outer = By("top.outer");
  ASSERT_NE(outer, nullptr);
  EXPECT_EQ(KindsOf(vpiStmt, outer),
            (std::vector<int>{vpiNamedBegin, vpiDisable}));
  vpiHandle it = vpi_iterate(vpiDisable, outer);
  ASSERT_NE(it, nullptr);
  EXPECT_EQ(VpiObjectOf(vpi_handle(vpiExpr, vpi_scan(it))),
            VpiObjectOf(By("top.outer.inner")));
}

TEST_F(DisablesOfARun, ADisableOfALaterProceduresBlockIsReached) {
  Run("module top;\n"
      "  initial #1 disable later;\n"
      "  initial begin : later #2; end\n"
      "endmodule\n");
  vpiHandle delay = NthBody(0);
  ASSERT_NE(delay, nullptr);
  vpiHandle disable = vpi_handle(vpiStmt, delay);
  ASSERT_NE(disable, nullptr);
  EXPECT_EQ(VpiObjectOf(vpi_handle(vpiExpr, disable)),
            VpiObjectOf(By("top.later")));
}

TEST_F(DisablesOfARun, ADisableOfAChildInstancesBlockIsReached) {
  Run("module child; initial begin : blk #2; end endmodule\n"
      "module top; child c(); initial #1 disable c.blk; endmodule\n");
  vpiHandle delay = NthBody(0);
  ASSERT_NE(delay, nullptr);
  vpiHandle disable = vpi_handle(vpiStmt, delay);
  ASSERT_NE(disable, nullptr);
  EXPECT_EQ(VpiObjectOf(vpi_handle(vpiExpr, disable)),
            VpiObjectOf(By("top.c.blk")));
}

TEST_F(DisablesOfARun, TheNearestBlockOfTheNameIsReachedWhereverWritten) {
  Run("module top;\n"
      "  initial begin : y #2; end\n"
      "  initial begin : outer\n"
      "    begin : x disable y; end\n"
      "    begin : y #2; end\n"
      "  end\n"
      "endmodule\n");
  vpiHandle x = By("top.outer.x");
  ASSERT_NE(x, nullptr);
  vpiHandle it = vpi_iterate(vpiDisable, x);
  ASSERT_NE(it, nullptr);
  EXPECT_EQ(VpiObjectOf(vpi_handle(vpiExpr, vpi_scan(it))),
            VpiObjectOf(By("top.outer.y")));
}

TEST_F(DisablesOfARun, ADisableForkReachesNothing) {
  Run("module top; initial begin fork #1; join_none disable fork; end\n"
      "endmodule\n");
  vpiHandle block = NthBody(0);
  ASSERT_NE(block, nullptr);
  EXPECT_EQ(KindsOf(vpiStmt, block),
            (std::vector<int>{vpiFork, vpiDisableFork}));
  vpiHandle it = vpi_iterate(vpiDisableFork, block);
  ASSERT_NE(it, nullptr);
  EXPECT_EQ(vpi_handle(vpiExpr, vpi_scan(it)), nullptr);
}

TEST(DisableModel, NoObjectHasNoDisableExpression) {
  EXPECT_EQ(VpiDisableExpr(nullptr), nullptr);
}

}  // namespace
}  // namespace delta
