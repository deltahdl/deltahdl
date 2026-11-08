#include <gtest/gtest.h>

#include <string>
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

class EventControl : public ::testing::Test {
 protected:
  void SetUp() override { SetGlobalVpiContext(&ctx_); }
  void TearDown() override { SetGlobalVpiContext(nullptr); }
  VpiContext ctx_;
};

TEST_F(EventControl, StandaloneEventControlReachesItsStatement) {
  VpiObject stmt;
  stmt.type = vpiBegin;

  VpiObject event_control;
  event_control.type = vpiEventControl;
  event_control.children = {&stmt};

  EXPECT_EQ(VpiEventControlStmt(&event_control), &stmt);

  VpiObject event_stmt;
  event_stmt.type = vpiEventStmt;
  event_control.parent = &event_stmt;
  EXPECT_EQ(VpiEventControlStmt(&event_control), &stmt);
}

TEST_F(EventControl, NullAndEmptyEventControlsReportNoStatement) {
  EXPECT_EQ(VpiEventControlStmt(nullptr), nullptr);

  VpiObject bare;
  bare.type = vpiEventControl;
  EXPECT_EQ(VpiEventControlStmt(&bare), nullptr);
}

TEST_F(EventControl, NullEventControlReportsNoCondition) {
  EXPECT_EQ(VpiEventControlConditionExpr(nullptr), nullptr);
}

TEST_F(EventControl, RuleAppliesThroughPublicVpiHandleDispatch) {
  VpiObject guarded;
  guarded.type = vpiBegin;

  VpiObject assignment;
  assignment.type = vpiAssignment;

  VpiObject on_assignment;
  on_assignment.type = vpiEventControl;
  on_assignment.parent = &assignment;
  on_assignment.children = {&guarded};
  EXPECT_EQ(vpi_handle(vpiStmt, VpiHandleOf(&on_assignment)), nullptr);

  VpiObject standalone;
  standalone.type = vpiEventControl;
  standalone.children = {&guarded};
  EXPECT_EQ(VpiObjectOf(vpi_handle(vpiStmt, VpiHandleOf(&standalone))),
            &guarded);
}

TEST_F(EventControl, ConditionRelationReachesEachEventOperandKind) {
  VpiObject expr_cond;
  expr_cond.type = vpiOperation;
  VpiObject on_expr;
  on_expr.type = vpiEventControl;
  on_expr.children = {&expr_cond};
  EXPECT_EQ(VpiObjectOf(vpi_handle(vpiCondition, VpiHandleOf(&on_expr))),
            &expr_cond);

  VpiObject seq_cond;
  seq_cond.type = vpiSequenceInst;
  VpiObject on_seq;
  on_seq.type = vpiEventControl;
  on_seq.children = {&seq_cond};
  EXPECT_EQ(VpiObjectOf(vpi_handle(vpiCondition, VpiHandleOf(&on_seq))),
            &seq_cond);

  VpiObject named_cond;
  named_cond.type = vpiNamedEvent;
  VpiObject on_named;
  on_named.type = vpiEventControl;
  on_named.children = {&named_cond};
  EXPECT_EQ(VpiObjectOf(vpi_handle(vpiCondition, VpiHandleOf(&on_named))),
            &named_cond);
}

TEST_F(EventControl, ConditionRelationIgnoresGuardedStatement) {
  VpiObject body;
  body.type = vpiBegin;

  VpiObject event_control;
  event_control.type = vpiEventControl;
  event_control.children = {&body};

  EXPECT_EQ(vpi_handle(vpiCondition, VpiHandleOf(&event_control)), nullptr);
}

class EventControlsOfARun : public VpiDesignRun {
 protected:
  static vpiHandle BodyOf(const std::string& scope) {
    vpiHandle it = vpi_iterate(vpiProcess, By(scope));
    return it == nullptr ? nullptr : vpi_handle(vpiStmt, vpi_scan(it));
  }

  static std::vector<vpiHandle> OperandsOf(vpiHandle op) {
    std::vector<vpiHandle> operands;
    vpiHandle it = vpi_iterate(vpiOperand, op);
    if (it == nullptr) return operands;
    while (vpiHandle operand = vpi_scan(it)) operands.push_back(operand);
    return operands;
  }
};

TEST_F(EventControlsOfARun, AnEventControlIsAnObjectOfTheRun) {
  Run("module top; bit clk; int q, d; always @(posedge clk) q <= d;\n"
      "endmodule\n");
  vpiHandle control = BodyOf("top");
  ASSERT_NE(control, nullptr);
  EXPECT_EQ(vpi_get(vpiType, control), vpiEventControl);
  vpiHandle condition = vpi_handle(vpiCondition, control);
  ASSERT_NE(condition, nullptr);
  EXPECT_EQ(vpi_get(vpiOpType, condition), vpiPosedgeOp);
  const std::vector<vpiHandle> kOperands = OperandsOf(condition);
  ASSERT_EQ(kOperands.size(), 1U);
  EXPECT_EQ(VpiObjectOf(kOperands[0]), VpiObjectOf(By("top.clk")));
  vpiHandle guarded = vpi_handle(vpiStmt, control);
  ASSERT_NE(guarded, nullptr);
  EXPECT_EQ(vpi_get(vpiType, guarded), vpiAssignment);
  EXPECT_EQ(vpi_get(vpiBlocking, guarded), 0);
  EXPECT_EQ(VpiObjectOf(vpi_handle(vpiScope, guarded)), VpiObjectOf(By("top")));
  EXPECT_EQ(VpiObjectOf(vpi_handle(vpiProcess, guarded)),
            VpiObjectOf(vpi_handle(vpiProcess, control)));
}

TEST_F(EventControlsOfARun, AnEdgeEventIsItsPosedgeOrItsNegedge) {
  Run("module top; bit clk; initial @(edge clk) ; endmodule\n");
  vpiHandle control = BodyOf("top");
  ASSERT_NE(control, nullptr);
  vpiHandle condition = vpi_handle(vpiCondition, control);
  ASSERT_NE(condition, nullptr);
  EXPECT_EQ(vpi_get(vpiOpType, condition), vpiEventOrOp);
  const std::vector<vpiHandle> kEdges = OperandsOf(condition);
  ASSERT_EQ(kEdges.size(), 2U);
  EXPECT_EQ(vpi_get(vpiOpType, kEdges[0]), vpiPosedgeOp);
  EXPECT_EQ(vpi_get(vpiOpType, kEdges[1]), vpiNegedgeOp);
  for (vpiHandle edge : kEdges) {
    const std::vector<vpiHandle> kSignal = OperandsOf(edge);
    ASSERT_EQ(kSignal.size(), 1U);
    EXPECT_EQ(VpiObjectOf(kSignal[0]), VpiObjectOf(By("top.clk")));
  }
}

TEST_F(EventControlsOfARun, ANamedEventIsTheConditionItself) {
  Run("module top; event e; initial @e ; endmodule\n");
  vpiHandle control = BodyOf("top");
  ASSERT_NE(control, nullptr);
  vpiHandle condition = vpi_handle(vpiCondition, control);
  ASSERT_NE(condition, nullptr);
  EXPECT_EQ(vpi_get(vpiType, condition), vpiNamedEvent);
  EXPECT_EQ(VpiObjectOf(condition), VpiObjectOf(By("top.e")));
  vpiHandle guarded = vpi_handle(vpiStmt, control);
  ASSERT_NE(guarded, nullptr);
  EXPECT_EQ(vpi_get(vpiType, guarded), vpiNullStmt);
}

TEST_F(EventControlsOfARun, AnEventListIsAnEventOrOperation) {
  Run("module top; bit a, b, c, en;\n"
      "  initial @(c, posedge a iff en or b) ;\n"
      "endmodule\n");
  vpiHandle control = BodyOf("top");
  ASSERT_NE(control, nullptr);
  vpiHandle outer = vpi_handle(vpiCondition, control);
  ASSERT_NE(outer, nullptr);
  EXPECT_EQ(vpi_get(vpiOpType, outer), vpiEventOrOp);
  const std::vector<vpiHandle> kOuter = OperandsOf(outer);
  ASSERT_EQ(kOuter.size(), 2U);
  EXPECT_EQ(VpiObjectOf(kOuter[1]), VpiObjectOf(By("top.b")));
  EXPECT_EQ(vpi_get(vpiOpType, kOuter[0]), vpiEventOrOp);
  const std::vector<vpiHandle> kInner = OperandsOf(kOuter[0]);
  ASSERT_EQ(kInner.size(), 2U);
  EXPECT_EQ(VpiObjectOf(kInner[0]), VpiObjectOf(By("top.c")));
  EXPECT_EQ(vpi_get(vpiOpType, kInner[1]), vpiIffOp);
  const std::vector<vpiHandle> kIff = OperandsOf(kInner[1]);
  ASSERT_EQ(kIff.size(), 2U);
  EXPECT_EQ(vpi_get(vpiOpType, kIff[0]), vpiPosedgeOp);
  EXPECT_EQ(VpiObjectOf(kIff[1]), VpiObjectOf(By("top.en")));
}

TEST_F(EventControlsOfARun, ASequenceEventIsItsSequenceInst) {
  Run("module top; bit clk, a, b;\n"
      "  sequence s; @(posedge clk) a ##1 b; endsequence\n"
      "  initial @(s) ;\n"
      "endmodule\n");
  vpiHandle control = BodyOf("top");
  ASSERT_NE(control, nullptr);
  vpiHandle condition = vpi_handle(vpiCondition, control);
  ASSERT_NE(condition, nullptr);
  EXPECT_EQ(vpi_get(vpiType, condition), vpiSequenceInst);
  vpiHandle decl = vpi_handle(vpiSequenceDecl, condition);
  ASSERT_NE(decl, nullptr);
  EXPECT_STREQ(vpi_get_str(vpiFullName, decl), "top.s");
}

TEST_F(EventControlsOfARun, AnImplicitEventListWritesNoCondition) {
  Run("module top; int a, b; always @* a = b; endmodule\n");
  vpiHandle control = BodyOf("top");
  ASSERT_NE(control, nullptr);
  EXPECT_EQ(vpi_get(vpiType, control), vpiEventControl);
  EXPECT_EQ(vpi_handle(vpiCondition, control), nullptr);
  vpiHandle guarded = vpi_handle(vpiStmt, control);
  ASSERT_NE(guarded, nullptr);
  EXPECT_EQ(vpi_get(vpiType, guarded), vpiAssignment);
}

}  // namespace
}  // namespace delta
