#include <gtest/gtest.h>

#include <cstddef>
#include <string>
#include <utility>
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

class ForFormsOfARun : public VpiDesignRun {
 protected:
  void SetUp() override {
    VpiDesignRun::SetUp();
    Run("module top; int i, j, k, s;\n"
        "  function void g(); endfunction\n"
        "  initial for (i = 0, k = 5; i < 3; i++, k--) s = i;\n"
        "  initial for (int a = 4, b = 7; a < b; a++, b--) ;\n"
        "  initial for (var int c = 0; c < 2; c++) ;\n"
        "  initial for (; i < 3; i++) ;\n"
        "  initial for (i = 3; i; i = i - 1) ;\n"
        "  initial for (;;) break;\n"
        "  initial for (i = 0; ; i++) break;\n"
        "  initial for (i = 0; i < 3; ++i) ;\n"
        "  initial for (i = 3; i > 0; i--) ;\n"
        "  initial for (i = 3; i > 0; --i) ;\n"
        "  initial for (i = 0; i < 6; i += 2) ;\n"
        "  initial for (i = 0; i < 3; g()) break;\n"
        "  initial for (i = 0; i < 3; i++) begin s = i; end\n"
        "  initial for (i = 0; i < 3; i++) begin : blk s = i; end\n"
        "  initial for (j = 0; j < 3; j++) for (k = 0; k < 3; k++) s = k;\n"
        "  initial for (int d = 9; d < 12; d++) ;\n"
        "endmodule\n");
  }

  static vpiHandle LoopAt(size_t n) {
    const std::vector<vpiHandle> kProcs = ObjectsOf(vpiProcess, By("top"));
    vpiHandle loop =
        n < kProcs.size() ? vpi_handle(vpiStmt, kProcs[n]) : nullptr;
    if (loop != nullptr) EXPECT_EQ(vpi_get(vpiType, loop), vpiFor);
    return loop;
  }

  static std::string LhsName(vpiHandle stmt) {
    vpiHandle lhs = stmt == nullptr ? nullptr : vpi_handle(vpiLhs, stmt);
    const char* name = lhs == nullptr ? nullptr : vpi_get_str(vpiName, lhs);
    return name == nullptr ? "" : name;
  }

  static std::vector<std::string> LhsNamesOf(int relation, vpiHandle loop) {
    std::vector<std::string> names;
    for (vpiHandle stmt : ObjectsOf(relation, loop)) {
      names.push_back(LhsName(stmt));
    }
    return names;
  }

  static int StepOp(size_t n) {
    vpiHandle step = vpi_handle(vpiForIncStmt, LoopAt(n));
    if (step == nullptr || vpi_get(vpiType, step) != vpiAssignment) return 0;
    return vpi_get(vpiOpType, step);
  }
};

TEST_F(ForFormsOfARun, AnInitializationListIsIteratedInTheOrderWritten) {
  vpiHandle loop = LoopAt(0);
  ASSERT_NE(loop, nullptr);
  EXPECT_EQ(LhsNamesOf(vpiForInitStmt, loop),
            (std::vector<std::string>{"i", "k"}));
  EXPECT_EQ(LhsName(vpi_handle(vpiForInitStmt, loop)), "i");
}

TEST_F(ForFormsOfARun, AStepListIsIteratedInTheOrderWritten) {
  vpiHandle loop = LoopAt(0);
  ASSERT_NE(loop, nullptr);
  const std::vector<vpiHandle> kSteps = ObjectsOf(vpiForIncStmt, loop);
  ASSERT_EQ(kSteps.size(), 2U);
  EXPECT_EQ(vpi_get(vpiOpType, kSteps[0]), vpiPostIncOp);
  EXPECT_EQ(LhsName(kSteps[0]), "i");
  EXPECT_EQ(vpi_get(vpiOpType, kSteps[1]), vpiPostDecOp);
  EXPECT_EQ(LhsName(kSteps[1]), "k");
  EXPECT_EQ(LhsName(vpi_handle(vpiForIncStmt, loop)), "i");
}

TEST_F(ForFormsOfARun, ADeclarationListIsOneDeclarationIteratedInOrder) {
  vpiHandle loop = LoopAt(1);
  ASSERT_NE(loop, nullptr);
  EXPECT_EQ(vpi_get(vpiLocalVarDecls, loop), 1);
  const std::vector<vpiHandle> kInits = ObjectsOf(vpiForInitStmt, loop);
  ASSERT_EQ(kInits.size(), 2U);
  EXPECT_EQ(IntegerOf(vpi_handle(vpiRhs, kInits[0])), 4);
  EXPECT_EQ(IntegerOf(vpi_handle(vpiRhs, kInits[1])), 7);
  EXPECT_EQ(ObjectsOf(vpiForIncStmt, loop).size(), 2U);
}

TEST_F(ForFormsOfARun, DISABLED_EachDeclaredInitializationNamesItsVariable) {
  EXPECT_EQ(LhsNamesOf(vpiForInitStmt, LoopAt(1)),
            (std::vector<std::string>{"a", "b"}));
  EXPECT_EQ(LhsName(vpi_handle(vpiForInitStmt, LoopAt(15))), "d");
}

TEST_F(ForFormsOfARun, ADeclaredVariableReachesItsFirstInitialization) {
  vpiHandle init = vpi_handle(vpiForInitStmt, LoopAt(15));
  ASSERT_NE(init, nullptr);
  EXPECT_EQ(vpi_get(vpiType, init), vpiAssignment);
  EXPECT_EQ(IntegerOf(vpi_handle(vpiRhs, init)), 9);
}

TEST_F(ForFormsOfARun, ADeclarationWithTheVarKeywordIsALocalDeclaration) {
  vpiHandle loop = LoopAt(2);
  ASSERT_NE(loop, nullptr);
  EXPECT_EQ(vpi_get(vpiLocalVarDecls, loop), 1);
}

TEST_F(ForFormsOfARun, AHeaderInitializingNothingDeclaresAndReachesNothing) {
  vpiHandle loop = LoopAt(3);
  ASSERT_NE(loop, nullptr);
  EXPECT_EQ(vpi_get(vpiLocalVarDecls, loop), 0);
  EXPECT_EQ(vpi_handle(vpiForInitStmt, loop), nullptr);
  EXPECT_EQ(vpi_iterate(vpiForInitStmt, loop), nullptr);
  EXPECT_EQ(OpOf(vpi_handle(vpiCondition, loop)), vpiLtOp);
  EXPECT_EQ(LhsName(vpi_handle(vpiForIncStmt, loop)), "i");
}

TEST_F(ForFormsOfARun, AVariableConditionIsAReferenceToTheVariable) {
  vpiHandle loop = LoopAt(4);
  ASSERT_NE(loop, nullptr);
  vpiHandle cond = vpi_handle(vpiCondition, loop);
  ASSERT_NE(cond, nullptr);
  EXPECT_EQ(VpiObjectOf(cond), VpiObjectOf(By("top.i")));
}

TEST_F(ForFormsOfARun, AnOmittedConditionIsNull) {
  vpiHandle bare = LoopAt(5);
  ASSERT_NE(bare, nullptr);
  EXPECT_EQ(vpi_handle(vpiCondition, bare), nullptr);
  EXPECT_EQ(vpi_handle(vpiForInitStmt, bare), nullptr);
  EXPECT_EQ(vpi_handle(vpiForIncStmt, bare), nullptr);
  EXPECT_EQ(vpi_get(vpiType, vpi_handle(vpiStmt, bare)), vpiBreak);
  vpiHandle stepped = LoopAt(6);
  ASSERT_NE(stepped, nullptr);
  EXPECT_EQ(vpi_handle(vpiCondition, stepped), nullptr);
  EXPECT_EQ(LhsName(vpi_handle(vpiForInitStmt, stepped)), "i");
  EXPECT_EQ(vpi_get(vpiOpType, vpi_handle(vpiForIncStmt, stepped)),
            vpiPostIncOp);
  EXPECT_EQ(vpi_get(vpiType, vpi_handle(vpiStmt, stepped)), vpiBreak);
}

TEST_F(ForFormsOfARun, EachIncrementOrDecrementStepGivesItsOperator) {
  EXPECT_EQ(StepOp(7), vpiPreIncOp);
  EXPECT_EQ(StepOp(8), vpiPostDecOp);
  EXPECT_EQ(StepOp(9), vpiPreDecOp);
}

TEST_F(ForFormsOfARun, AnOperatorAssignmentStepGivesItsOperator) {
  EXPECT_EQ(StepOp(10), vpiAddOp);
  vpiHandle step = vpi_handle(vpiForIncStmt, LoopAt(10));
  ASSERT_NE(step, nullptr);
  EXPECT_EQ(IntegerOf(vpi_handle(vpiRhs, step)), 2);
}

TEST_F(ForFormsOfARun, AFunctionCallStepIsTheIncrementStatement) {
  vpiHandle step = vpi_handle(vpiForIncStmt, LoopAt(11));
  ASSERT_NE(step, nullptr);
  EXPECT_EQ(vpi_get(vpiType, step), vpiFuncCall);
  EXPECT_EQ(CalleeOf(step), "g");
}

TEST_F(ForFormsOfARun, EachBodyKindIsReachedAsItsOwnKind) {
  const std::vector<std::pair<size_t, int>> kBodies{
      {12, vpiBegin}, {13, vpiNamedBegin}, {7, vpiNullStmt}, {14, vpiFor}};
  for (const auto& [n, kind] : kBodies) {
    vpiHandle body = vpi_handle(vpiStmt, LoopAt(n));
    ASSERT_NE(body, nullptr) << n;
    EXPECT_EQ(vpi_get(vpiType, body), kind) << n;
  }
  vpiHandle inner = vpi_handle(vpiStmt, LoopAt(14));
  ASSERT_NE(inner, nullptr);
  EXPECT_EQ(LhsName(vpi_handle(vpiForInitStmt, inner)), "k");
}

TEST_F(ForLoopsOfARun, AForInEachPlaceIsAForObject) {
  Run("package pk; int i; task pt; for (i = 0; i < 2; i++) ; endtask\n"
      "endpackage\n"
      "interface ifc; int i; initial for (i = 0; i < 2; i++) ; endinterface\n"
      "program prg; int i; initial for (i = 0; i < 2; i++) ; endprogram\n"
      "module top; int i; ifc i0(); prg p0();\n"
      "  class C; int i;\n"
      "    function void cm; for (i = 0; i < 2; i++) ; endfunction\n"
      "  endclass\n"
      "  task tk; for (i = 0; i < 2; i++) ; endtask\n"
      "  function void fn; for (i = 0; i < 2; i++) ; endfunction\n"
      "endmodule\n");
  std::vector<std::pair<const char*, vpiHandle>> owners =
      OwnersInEachPlace("cm");
  owners.emplace_back("module function", Named(vpiFunction, By("top"), "fn"));
  for (const auto& [where, owner] : owners) {
    ASSERT_NE(owner, nullptr) << where;
    vpiHandle loop = vpi_handle(vpiStmt, owner);
    ASSERT_NE(loop, nullptr) << where;
    EXPECT_EQ(vpi_get(vpiType, loop), vpiFor) << where;
    EXPECT_EQ(OpOf(vpi_handle(vpiCondition, loop)), vpiLtOp) << where;
    EXPECT_EQ(vpi_get(vpiType, vpi_handle(vpiForInitStmt, loop)), vpiAssignment)
        << where;
    EXPECT_EQ(vpi_get(vpiOpType, vpi_handle(vpiForIncStmt, loop)), vpiPostIncOp)
        << where;
    EXPECT_EQ(vpi_get(vpiType, vpi_handle(vpiStmt, loop)), vpiNullStmt)
        << where;
  }
}

}  // namespace
}  // namespace delta
