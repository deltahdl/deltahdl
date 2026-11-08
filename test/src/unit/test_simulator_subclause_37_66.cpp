#include <gtest/gtest.h>

#include "fixture_vpi_run.h"
#include "simulator/sv_vpi_user.h"
#include "simulator/vpi_context.h"
#include "simulator/vpi_globals.h"
#include "simulator/vpi_model_helpers1.h"
#include "simulator/vpi_object.h"
#include "simulator/vpi_user.h"

namespace delta {
namespace {

class WhileRepeat : public ::testing::Test {
 protected:
  void SetUp() override { SetGlobalVpiContext(&ctx_); }
  void TearDown() override { SetGlobalVpiContext(nullptr); }
  VpiContext ctx_;
};

TEST_F(WhileRepeat, WhileStatementReachesConditionThroughVpiCondition) {
  VpiObject condition;
  condition.type = vpiOperation;

  VpiObject body;
  body.type = vpiBegin;

  VpiObject while_stmt;
  while_stmt.type = vpiWhile;
  while_stmt.children = {&condition, &body};

  EXPECT_EQ(VpiObjectOf(vpi_handle(vpiCondition, VpiHandleOf(&while_stmt))),
            &condition);
}

TEST_F(WhileRepeat, RepeatStatementReachesConditionThroughVpiCondition) {
  VpiObject condition;
  condition.type = vpiRefObj;

  VpiObject repeat_stmt;
  repeat_stmt.type = vpiRepeat;
  repeat_stmt.children = {&condition};

  EXPECT_EQ(VpiObjectOf(vpi_handle(vpiCondition, VpiHandleOf(&repeat_stmt))),
            &condition);
}

TEST_F(WhileRepeat, ConditionFoundWhenItFollowsTheBodyChild) {
  VpiObject body;
  body.type = vpiBegin;

  VpiObject condition;
  condition.type = vpiOperation;

  VpiObject while_stmt;
  while_stmt.type = vpiWhile;
  while_stmt.children = {&body, &condition};

  EXPECT_EQ(VpiObjectOf(vpi_handle(vpiCondition, VpiHandleOf(&while_stmt))),
            &condition);
}

TEST_F(WhileRepeat, ConditionIsNullWhenAbsentOrHandleNull) {
  EXPECT_EQ(VpiLoopConditionExpr(nullptr), nullptr);

  VpiObject body;
  body.type = vpiBegin;

  VpiObject bare_loop;
  bare_loop.type = vpiWhile;
  bare_loop.children = {&body};
  EXPECT_EQ(VpiLoopConditionExpr(&bare_loop), nullptr);

  VpiObject condition;
  condition.type = vpiOperation;
  VpiObject if_stmt;
  if_stmt.type = vpiIf;
  if_stmt.children = {&condition};
  EXPECT_EQ(VpiLoopConditionExpr(&if_stmt), nullptr);
}

TEST_F(WhileRepeat, VpiConditionIsScopedToLoopStatements) {
  VpiObject condition;
  condition.type = vpiOperation;

  VpiObject forever_stmt;
  forever_stmt.type = vpiForever;
  forever_stmt.children = {&condition};

  EXPECT_EQ(vpi_handle(vpiCondition, VpiHandleOf(&forever_stmt)), nullptr);
}

TEST_F(WhileRepeat, LoopBodyReachedByTheKindTheStmtClassGroups) {
  VpiObject condition;
  condition.type = vpiOperation;

  VpiObject body;
  body.type = vpiBegin;

  VpiObject while_stmt;
  while_stmt.type = vpiWhile;
  while_stmt.children = {&condition, &body};

  EXPECT_EQ(VpiObjectOf(vpi_handle(vpiStmt, VpiHandleOf(&while_stmt))), &body);

  VpiObject repeat_body;
  repeat_body.type = vpiAssignment;

  VpiObject repeat_stmt;
  repeat_stmt.type = vpiRepeat;
  repeat_stmt.children = {&condition, &repeat_body};

  EXPECT_EQ(VpiObjectOf(vpi_handle(vpiStmt, VpiHandleOf(&repeat_stmt))),
            &repeat_body);
}

TEST_F(WhileRepeat, TheConditionExpressionIsNotTakenForTheBody) {
  VpiObject condition;
  condition.type = vpiOperation;

  VpiObject while_stmt;
  while_stmt.type = vpiWhile;
  while_stmt.children = {&condition};

  EXPECT_EQ(vpi_handle(vpiStmt, VpiHandleOf(&while_stmt)), nullptr);
  EXPECT_EQ(VpiObjectOf(vpi_handle(vpiCondition, VpiHandleOf(&while_stmt))),
            &condition);
}

class WhileAndRepeatLoopsOfARun : public VpiDesignRun {
 protected:
  static vpiHandle LoopOf(const char* scope) {
    vpiHandle it = vpi_iterate(vpiProcess, By(scope));
    return it == nullptr ? nullptr : vpi_handle(vpiStmt, vpi_scan(it));
  }
};

TEST_F(WhileAndRepeatLoopsOfARun, AWhileLoopIsAnObjectOfTheRun) {
  Run("module top; int i; initial while (i < 3) i = i + 1; endmodule\n");
  vpiHandle loop = LoopOf("top");
  ASSERT_NE(loop, nullptr);
  EXPECT_EQ(vpi_get(vpiType, loop), vpiWhile);
  vpiHandle condition = vpi_handle(vpiCondition, loop);
  ASSERT_NE(condition, nullptr);
  EXPECT_EQ(vpi_get(vpiOpType, condition), vpiLtOp);
  vpiHandle body = vpi_handle(vpiStmt, loop);
  ASSERT_NE(body, nullptr);
  EXPECT_EQ(vpi_get(vpiType, body), vpiAssignment);
}

TEST_F(WhileAndRepeatLoopsOfARun, ARepeatLoopReachesItsCount) {
  Run("module top; int n = 2; initial repeat (n) #1 ; endmodule\n");
  vpiHandle loop = LoopOf("top");
  ASSERT_NE(loop, nullptr);
  EXPECT_EQ(vpi_get(vpiType, loop), vpiRepeat);
  EXPECT_EQ(VpiObjectOf(vpi_handle(vpiCondition, loop)),
            VpiObjectOf(By("top.n")));
  vpiHandle body = vpi_handle(vpiStmt, loop);
  ASSERT_NE(body, nullptr);
  EXPECT_EQ(vpi_get(vpiType, body), vpiDelayControl);
}

}  // namespace
}  // namespace delta
