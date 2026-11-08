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

class IfIfElse : public ::testing::Test {
 protected:
  void SetUp() override { SetGlobalVpiContext(&ctx_); }
  void TearDown() override { SetGlobalVpiContext(nullptr); }
  VpiContext ctx_;
};

TEST_F(IfIfElse, IfStatementReachesConditionThroughVpiCondition) {
  VpiObject condition;
  condition.type = vpiOperation;

  VpiObject then_body;
  then_body.type = vpiBegin;

  VpiObject if_stmt;
  if_stmt.type = vpiIf;
  if_stmt.children = {&condition, &then_body};

  EXPECT_EQ(VpiObjectOf(vpi_handle(vpiCondition, VpiHandleOf(&if_stmt))),
            &condition);
}

TEST_F(IfIfElse, IfElseStatementReachesConditionThroughVpiCondition) {
  VpiObject condition;
  condition.type = vpiRefObj;

  VpiObject then_body;
  then_body.type = vpiBegin;

  VpiObject else_body;
  else_body.type = vpiAssignment;

  VpiObject if_else;
  if_else.type = vpiIfElse;
  if_else.children = {&condition, &then_body, &else_body};

  EXPECT_EQ(VpiObjectOf(vpi_handle(vpiCondition, VpiHandleOf(&if_else))),
            &condition);
}

TEST_F(IfIfElse, ConditionFoundWhenItFollowsABodyChild) {
  VpiObject then_body;
  then_body.type = vpiBegin;

  VpiObject condition;
  condition.type = vpiOperation;

  VpiObject if_stmt;
  if_stmt.type = vpiIf;
  if_stmt.children = {&then_body, &condition};

  EXPECT_EQ(VpiObjectOf(vpi_handle(vpiCondition, VpiHandleOf(&if_stmt))),
            &condition);
}

TEST_F(IfIfElse, VpiConditionIsScopedToConditionalStatements) {
  VpiObject expr;
  expr.type = vpiOperation;

  VpiObject other;
  other.type = vpiRepeatControl;
  other.children = {&expr};

  EXPECT_EQ(vpi_handle(vpiCondition, VpiHandleOf(&other)), nullptr);
}

TEST_F(IfIfElse, ConditionIsNullWhenNoExpressionChild) {
  VpiObject then_body;
  then_body.type = vpiBegin;

  VpiObject if_stmt;
  if_stmt.type = vpiIf;
  if_stmt.children = {&then_body};

  EXPECT_EQ(VpiObjectOf(vpi_handle(vpiStmt, VpiHandleOf(&if_stmt))),
            &then_body);
  EXPECT_EQ(vpi_handle(vpiCondition, VpiHandleOf(&if_stmt)), nullptr);
}

TEST_F(IfIfElse, ThenBodyReachedByTheKindTheStmtClassGroups) {
  VpiObject condition;
  condition.type = vpiOperation;

  VpiObject then_body;
  then_body.type = vpiBegin;

  VpiObject else_body;
  else_body.type = vpiAssignment;

  VpiObject if_else;
  if_else.type = vpiIfElse;
  if_else.children = {&condition, &then_body, &else_body};

  EXPECT_EQ(VpiObjectOf(vpi_handle(vpiStmt, VpiHandleOf(&if_else))),
            &then_body);
}

TEST_F(IfIfElse, PlainIfReachesEachKindAThenBranchCarries) {
  for (int body_kind :
       {vpiAssignment, vpiNamedBegin, vpiFork, vpiIf, vpiNullStmt}) {
    VpiObject condition;
    condition.type = vpiOperation;

    VpiObject then_body;
    then_body.type = body_kind;

    VpiObject if_stmt;
    if_stmt.type = vpiIf;
    if_stmt.children = {&condition, &then_body};

    EXPECT_EQ(VpiObjectOf(vpi_handle(vpiStmt, VpiHandleOf(&if_stmt))),
              &then_body)
        << "then-branch kind " << body_kind;
  }
}

TEST_F(IfIfElse, IfElseStatementReachesElseBranchThroughVpiElseStmt) {
  VpiObject condition;
  condition.type = vpiOperation;

  VpiObject then_body;
  then_body.type = vpiBegin;

  VpiObject else_body;
  else_body.type = vpiAssignment;

  VpiObject if_else;
  if_else.type = vpiIfElse;
  if_else.children = {&condition, &then_body, &else_body};

  EXPECT_EQ(VpiObjectOf(vpi_handle(vpiStmt, VpiHandleOf(&if_else))),
            &then_body);
  EXPECT_EQ(VpiObjectOf(vpi_handle(vpiElseStmt, VpiHandleOf(&if_else))),
            &else_body);
}

TEST_F(IfIfElse, ElseBranchWrittenAsANestedConditionalIsTheSecondStatement) {
  VpiObject condition;
  condition.type = vpiOperation;

  VpiObject then_body;
  then_body.type = vpiIf;

  VpiObject else_body;
  else_body.type = vpiIf;

  VpiObject if_else;
  if_else.type = vpiIfElse;
  if_else.children = {&condition, &then_body, &else_body};

  EXPECT_EQ(VpiObjectOf(vpi_handle(vpiStmt, VpiHandleOf(&if_else))),
            &then_body);
  EXPECT_EQ(VpiObjectOf(vpi_handle(vpiElseStmt, VpiHandleOf(&if_else))),
            &else_body);
}

TEST_F(IfIfElse, PlainIfReportsNoElseStatement) {
  VpiObject condition;
  condition.type = vpiOperation;

  VpiObject then_body;
  then_body.type = vpiBegin;

  VpiObject second_body;
  second_body.type = vpiAssignment;

  VpiObject if_stmt;
  if_stmt.type = vpiIf;
  if_stmt.children = {&condition, &then_body, &second_body};

  EXPECT_EQ(vpi_handle(vpiElseStmt, VpiHandleOf(&if_stmt)), nullptr);
}

TEST_F(IfIfElse, ElseStatementIsNullWhenNoElseBranch) {
  VpiObject condition;
  condition.type = vpiOperation;

  VpiObject then_body;
  then_body.type = vpiBegin;

  VpiObject if_else;
  if_else.type = vpiIfElse;
  if_else.children = {&condition, &then_body};

  EXPECT_EQ(vpi_handle(vpiElseStmt, VpiHandleOf(&if_else)), nullptr);
  EXPECT_EQ(VpiIfElseStmt(nullptr), nullptr);
}

TEST_F(IfIfElse, ConditionalStatementReportsQualifier) {
  VpiObject if_stmt;
  if_stmt.type = vpiIf;
  if_stmt.qualifier = vpiUniqueQualifier;
  EXPECT_EQ(vpi_get(vpiQualifier, VpiHandleOf(&if_stmt)), vpiUniqueQualifier);

  VpiObject if_else;
  if_else.type = vpiIfElse;
  if_else.qualifier = vpiPriorityQualifier;
  EXPECT_EQ(vpi_get(vpiQualifier, VpiHandleOf(&if_else)), vpiPriorityQualifier);

  VpiObject plain_if;
  plain_if.type = vpiIf;
  EXPECT_EQ(vpi_get(vpiQualifier, VpiHandleOf(&plain_if)), vpiNoQualifier);
}

class IfStatementsOfARun : public VpiDesignRun {
 protected:
  static std::vector<vpiHandle> Bodies() {
    std::vector<vpiHandle> bodies;
    vpiHandle it = vpi_iterate(vpiProcess, By("top"));
    while (vpiHandle proc = it ? vpi_scan(it) : nullptr) {
      bodies.push_back(vpi_handle(vpiStmt, proc));
    }
    return bodies;
  }
};

TEST_F(IfStatementsOfARun, AnIfIsAnObjectOfTheRun) {
  Run("module top; int a, b; initial if (a) b = 1; endmodule\n");
  const std::vector<vpiHandle> kBodies = Bodies();
  ASSERT_EQ(kBodies.size(), 1U);
  vpiHandle branch = kBodies[0];
  ASSERT_NE(branch, nullptr);
  EXPECT_EQ(vpi_get(vpiType, branch), vpiIf);
  EXPECT_EQ(vpi_get(vpiQualifier, branch), vpiNoQualifier);
  EXPECT_EQ(VpiObjectOf(vpi_handle(vpiCondition, branch)),
            VpiObjectOf(By("top.a")));
  vpiHandle then = vpi_handle(vpiStmt, branch);
  ASSERT_NE(then, nullptr);
  EXPECT_EQ(vpi_get(vpiType, then), vpiAssignment);
  EXPECT_EQ(vpi_handle(vpiElseStmt, branch), nullptr);
}

TEST_F(IfStatementsOfARun, AnIfElseReachesBothBranches) {
  Run("module top; int a, b;\n"
      "  initial unique if (a == 1) b = 1; else b = 2;\n"
      "  initial priority if (a) b = 1; else if (b) a = 2;\n"
      "endmodule\n");
  const std::vector<vpiHandle> kBodies = Bodies();
  ASSERT_EQ(kBodies.size(), 2U);
  vpiHandle unique = kBodies[0];
  ASSERT_NE(unique, nullptr);
  EXPECT_EQ(vpi_get(vpiType, unique), vpiIfElse);
  EXPECT_EQ(vpi_get(vpiQualifier, unique), vpiUniqueQualifier);
  EXPECT_EQ(vpi_get(vpiOpType, vpi_handle(vpiCondition, unique)), vpiEqOp);
  vpiHandle then = vpi_handle(vpiStmt, unique);
  vpiHandle otherwise = vpi_handle(vpiElseStmt, unique);
  ASSERT_NE(then, nullptr);
  ASSERT_NE(otherwise, nullptr);
  EXPECT_NE(VpiObjectOf(then), VpiObjectOf(otherwise));
  EXPECT_EQ(vpi_get(vpiType, otherwise), vpiAssignment);
  vpiHandle priority = kBodies[1];
  ASSERT_NE(priority, nullptr);
  EXPECT_EQ(vpi_get(vpiQualifier, priority), vpiPriorityQualifier);
  vpiHandle nested = vpi_handle(vpiElseStmt, priority);
  ASSERT_NE(nested, nullptr);
  EXPECT_EQ(vpi_get(vpiType, nested), vpiIf);
}

TEST_F(IfStatementsOfARun, AnElseBranchIsReachedWhateverTheThenBranchIs) {
  Run("module top; int c, i, j;\n"
      "  initial if (c) i++; else j = 1;\n"
      "endmodule\n");
  const std::vector<vpiHandle> kBodies = Bodies();
  ASSERT_EQ(kBodies.size(), 1U);
  vpiHandle branch = kBodies[0];
  ASSERT_NE(branch, nullptr);
  vpiHandle otherwise = vpi_handle(vpiElseStmt, branch);
  ASSERT_NE(otherwise, nullptr);
  EXPECT_EQ(vpi_get(vpiType, otherwise), vpiAssignment);
  EXPECT_EQ(VpiObjectOf(vpi_handle(vpiLhs, otherwise)),
            VpiObjectOf(By("top.j")));
  EXPECT_NE(VpiObjectOf(vpi_handle(vpiStmt, branch)), VpiObjectOf(otherwise));
}

TEST_F(IfStatementsOfARun, AUnique0IfReportsTheUniqueQualifier) {
  Run("module top; int a, b;\n"
      "  initial unique0 if (a) b = 1;\n"
      "  initial unique0 if (a == 1) b = 1; else if (a == 2) b = 2;\n"
      "endmodule\n");
  const std::vector<vpiHandle> kBodies = Bodies();
  ASSERT_EQ(kBodies.size(), 2U);
  ASSERT_NE(kBodies[0], nullptr);
  ASSERT_NE(kBodies[1], nullptr);
  EXPECT_EQ(vpi_get(vpiType, kBodies[0]), vpiIf);
  EXPECT_EQ(vpi_get(vpiQualifier, kBodies[0]), vpiUniqueQualifier);
  EXPECT_EQ(vpi_get(vpiType, kBodies[1]), vpiIfElse);
  EXPECT_EQ(vpi_get(vpiQualifier, kBodies[1]), vpiUniqueQualifier);
}

TEST(IfModel, NoObjectHasNoCondition) {
  EXPECT_EQ(VpiIfConditionExpr(nullptr), nullptr);
}

}  // namespace
}  // namespace delta
