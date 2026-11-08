#include <gtest/gtest.h>

#include <vector>

#include "fixture_vpi_run.h"
#include "simulator/sv_vpi_user.h"
#include "simulator/vpi_context.h"
#include "simulator/vpi_globals.h"
#include "simulator/vpi_internal.h"
#include "simulator/vpi_model_helpers1.h"
#include "simulator/vpi_object.h"
#include "simulator/vpi_user.h"

namespace delta {
namespace {

class For : public ::testing::Test {
 protected:
  void SetUp() override { SetGlobalVpiContext(&ctx_); }
  void TearDown() override { SetGlobalVpiContext(nullptr); }
  VpiContext ctx_;
};

TEST_F(For, ForStatementReachesConditionAmongItsChildren) {
  VpiObject body;
  body.type = vpiBegin;
  VpiObject condition;
  condition.type = vpiOperation;

  VpiObject for_stmt;
  for_stmt.type = vpiFor;
  for_stmt.children = {&body, &condition};

  EXPECT_EQ(VpiObjectOf(vpi_handle(vpiCondition, VpiHandleOf(&for_stmt))),
            &condition);
}

TEST_F(For, ForWithoutConditionReportsNoCondition) {
  VpiObject body;
  body.type = vpiBegin;

  VpiObject for_stmt;
  for_stmt.type = vpiFor;
  for_stmt.children = {&body};

  EXPECT_EQ(vpi_handle(vpiCondition, VpiHandleOf(&for_stmt)), nullptr);
}

TEST_F(For, ForConditionRelationIsScopedToForStatements) {
  VpiObject expr;
  expr.type = vpiOperation;

  VpiObject not_a_for;
  not_a_for.type = vpiBegin;
  not_a_for.children = {&expr};

  EXPECT_EQ(vpi_handle(vpiCondition, VpiHandleOf(&not_a_for)), nullptr);
}

TEST_F(For, InitializationStatementsReachedThroughTheVpiForInitStmtIteration) {
  VpiObject init0;
  init0.type = vpiAssignment;
  VpiObject init1;
  init1.type = vpiAssignment;
  VpiObject increment;
  increment.type = vpiAssignment;
  VpiObject body;
  body.type = vpiBegin;

  VpiObject for_stmt;
  for_stmt.type = vpiFor;
  for_stmt.children = {&body};
  for_stmt.for_init_stmts = {&init0, &init1};
  for_stmt.for_inc_stmts = {&increment};

  VpiHandle it = ctx_.Iterate(vpiForInitStmt, &for_stmt);
  ASSERT_NE(it, nullptr);
  EXPECT_EQ(ctx_.Scan(it), &init0);
  EXPECT_EQ(ctx_.Scan(it), &init1);
  EXPECT_EQ(ctx_.Scan(it), nullptr);
}

TEST_F(For, IncrementStatementsReachedThroughTheVpiForIncStmtIteration) {
  VpiObject init;
  init.type = vpiAssignment;
  VpiObject increment0;
  increment0.type = vpiAssignment;
  VpiObject increment1;
  increment1.type = vpiAssignment;
  VpiObject body;
  body.type = vpiBegin;

  VpiObject for_stmt;
  for_stmt.type = vpiFor;
  for_stmt.children = {&body};
  for_stmt.for_init_stmts = {&init};
  for_stmt.for_inc_stmts = {&increment0, &increment1};

  VpiHandle it = ctx_.Iterate(vpiForIncStmt, &for_stmt);
  ASSERT_NE(it, nullptr);
  EXPECT_EQ(ctx_.Scan(it), &increment0);
  EXPECT_EQ(ctx_.Scan(it), &increment1);
  EXPECT_EQ(ctx_.Scan(it), nullptr);
}

TEST_F(For, SingleArrowsReachTheFirstStatementOfEachPartOfTheHeader) {
  VpiObject init0;
  init0.type = vpiAssignment;
  VpiObject init1;
  init1.type = vpiAssignment;
  VpiObject increment0;
  increment0.type = vpiAssignment;
  VpiObject increment1;
  increment1.type = vpiAssignment;

  VpiObject for_stmt;
  for_stmt.type = vpiFor;
  for_stmt.for_init_stmts = {&init0, &init1};
  for_stmt.for_inc_stmts = {&increment0, &increment1};

  EXPECT_EQ(VpiObjectOf(vpi_handle(vpiForInitStmt, VpiHandleOf(&for_stmt))),
            &init0);
  EXPECT_EQ(VpiObjectOf(vpi_handle(vpiForIncStmt, VpiHandleOf(&for_stmt))),
            &increment0);
}

TEST_F(For, AHeaderThatWritesNeitherPartReachesNothingByEitherRelation) {
  VpiObject body;
  body.type = vpiBegin;

  VpiObject for_stmt;
  for_stmt.type = vpiFor;
  for_stmt.children = {&body};

  EXPECT_EQ(ctx_.Iterate(vpiForInitStmt, &for_stmt), nullptr);
  EXPECT_EQ(ctx_.Iterate(vpiForIncStmt, &for_stmt), nullptr);
  EXPECT_EQ(vpi_handle(vpiForInitStmt, VpiHandleOf(&for_stmt)), nullptr);
  EXPECT_EQ(vpi_handle(vpiForIncStmt, VpiHandleOf(&for_stmt)), nullptr);
}

TEST_F(For, HeaderRelationsAreScopedToForStatements) {
  VpiObject body;
  body.type = vpiBegin;

  VpiObject not_a_for;
  not_a_for.type = vpiWhile;
  not_a_for.children = {&body};

  EXPECT_EQ(vpi_handle(vpiForInitStmt, VpiHandleOf(&not_a_for)), nullptr);
  EXPECT_EQ(ctx_.Iterate(vpiForInitStmt, &not_a_for), nullptr);
}

TEST_F(For, ForStatementReachesBodyByTheKindTheStmtClassGroups) {
  VpiObject condition;
  condition.type = vpiOperation;
  VpiObject init;
  init.type = vpiAssignment;
  VpiObject body;
  body.type = vpiBegin;

  VpiObject for_stmt;
  for_stmt.type = vpiFor;
  for_stmt.children = {&condition, &body};
  for_stmt.for_init_stmts = {&init};

  EXPECT_EQ(VpiObjectOf(vpi_handle(vpiStmt, VpiHandleOf(&for_stmt))), &body);
}

TEST_F(For, EachKindABodyCarriesIsReached) {
  for (int body_kind :
       {vpiAssignment, vpiNamedBegin, vpiFork, vpiFor, vpiNullStmt}) {
    VpiObject body;
    body.type = body_kind;

    VpiObject for_stmt;
    for_stmt.type = vpiFor;
    for_stmt.children = {&body};

    EXPECT_EQ(VpiObjectOf(vpi_handle(vpiStmt, VpiHandleOf(&for_stmt))), &body)
        << "body kind " << body_kind;
  }
}

TEST_F(For, ForWithoutBodyReportsNoStatement) {
  VpiObject condition;
  condition.type = vpiOperation;
  VpiObject init;
  init.type = vpiAssignment;
  VpiObject increment;
  increment.type = vpiAssignment;

  VpiObject for_stmt;
  for_stmt.type = vpiFor;
  for_stmt.children = {&condition};
  for_stmt.for_init_stmts = {&init};
  for_stmt.for_inc_stmts = {&increment};

  EXPECT_EQ(vpi_handle(vpiStmt, VpiHandleOf(&for_stmt)), nullptr);
}

class ForLoopsOfARun : public VpiDesignRun {
 protected:
  static vpiHandle TheLoop() {
    vpiHandle it = vpi_iterate(vpiProcess, By("top"));
    vpiHandle loop = it ? vpi_handle(vpiStmt, vpi_scan(it)) : nullptr;
    if (loop != nullptr) EXPECT_EQ(vpi_get(vpiType, loop), vpiFor);
    return loop;
  }
};

TEST_F(ForLoopsOfARun, AForLoopIsAnObjectOfTheRun) {
  Run("module top; int i, s;\n"
      "  initial for (i = 0; i < 3; i = i + 1) s = i;\n"
      "endmodule\n");
  vpiHandle loop = TheLoop();
  ASSERT_NE(loop, nullptr);
  EXPECT_EQ(vpi_get(vpiLocalVarDecls, loop), 0);
  vpiHandle init = vpi_handle(vpiForInitStmt, loop);
  vpiHandle step = vpi_handle(vpiForIncStmt, loop);
  ASSERT_NE(init, nullptr);
  ASSERT_NE(step, nullptr);
  EXPECT_EQ(vpi_get(vpiType, init), vpiAssignment);
  EXPECT_EQ(VpiObjectOf(vpi_handle(vpiLhs, init)), VpiObjectOf(By("top.i")));
  EXPECT_EQ(vpi_get(vpiOpType, vpi_handle(vpiRhs, step)), vpiAddOp);
  EXPECT_EQ(vpi_get(vpiOpType, vpi_handle(vpiCondition, loop)), vpiLtOp);
  vpiHandle body = vpi_handle(vpiStmt, loop);
  ASSERT_NE(body, nullptr);
  EXPECT_EQ(VpiObjectOf(vpi_handle(vpiLhs, body)), VpiObjectOf(By("top.s")));
}

TEST_F(ForLoopsOfARun, AnIncrementStepIsTheLoopsIncrementStatement) {
  Run("module top; int i, s;\n"
      "  initial for (i = 0; i < 3; i++) s = i;\n"
      "endmodule\n");
  vpiHandle loop = TheLoop();
  ASSERT_NE(loop, nullptr);
  vpiHandle step = vpi_handle(vpiForIncStmt, loop);
  ASSERT_NE(step, nullptr);
  EXPECT_EQ(vpi_get(vpiType, step), vpiAssignment);
  EXPECT_EQ(vpi_get(vpiOpType, step), vpiPostIncOp);
  EXPECT_EQ(VpiObjectOf(vpi_handle(vpiLhs, step)), VpiObjectOf(By("top.i")));
}

TEST_F(ForLoopsOfARun, AForLoopDeclaringItsVariableIsAScope) {
  Run("module top; initial for (int j = 0; j < 2; j = j + 1) ; endmodule\n");
  vpiHandle loop = TheLoop();
  ASSERT_NE(loop, nullptr);
  EXPECT_EQ(vpi_get(vpiLocalVarDecls, loop), 1);
  EXPECT_EQ(KindsOf(vpiInternalScope, By("top")), std::vector<int>{vpiFor});
}

TEST_F(For, NoConditionOrHeaderStatementWithoutAForStatement) {
  EXPECT_EQ(VpiForConditionExpr(nullptr), nullptr);
  EXPECT_EQ(VpiForHeaderStmt(vpiForInitStmt, nullptr), nullptr);
  VpiObject init;
  init.type = vpiAssignment;
  VpiObject while_stmt;
  while_stmt.type = vpiWhile;
  while_stmt.for_init_stmts = {&init};
  EXPECT_EQ(VpiForHeaderStmt(vpiForInitStmt, &while_stmt), nullptr);
}

}  // namespace
}  // namespace delta
