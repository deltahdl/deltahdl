#include <gtest/gtest.h>

#include <array>
#include <cstddef>
#include <string>

#include "fixture_vpi_run.h"
#include "simulator/sv_vpi_user.h"
#include "simulator/vpi_context.h"
#include "simulator/vpi_globals.h"
#include "simulator/vpi_model_helpers1.h"
#include "simulator/vpi_object.h"
#include "simulator/vpi_user.h"

namespace delta {
namespace {

class Assignment : public ::testing::Test {
 protected:
  void SetUp() override { SetGlobalVpiContext(&ctx_); }
  void TearDown() override { SetGlobalVpiContext(nullptr); }
  VpiContext ctx_;
};

TEST_F(Assignment, NormalAssignmentsReportVpiAssignmentOp) {
  EXPECT_EQ(VpiAssignmentOpType("="), vpiAssignmentOp);
  EXPECT_EQ(VpiAssignmentOpType("<="), vpiAssignmentOp);
}

TEST_F(Assignment, AssignmentOperatorsReportTheCombinedOperator) {
  EXPECT_EQ(VpiAssignmentOpType("+="), vpiAddOp);
  EXPECT_EQ(VpiAssignmentOpType("-="), vpiSubOp);
  EXPECT_EQ(VpiAssignmentOpType("*="), vpiMultOp);
  EXPECT_EQ(VpiAssignmentOpType("/="), vpiDivOp);
  EXPECT_EQ(VpiAssignmentOpType("%="), vpiModOp);
  EXPECT_EQ(VpiAssignmentOpType("&="), vpiBitAndOp);
  EXPECT_EQ(VpiAssignmentOpType("|="), vpiBitOrOp);
  EXPECT_EQ(VpiAssignmentOpType("^="), vpiBitXorOp);
  EXPECT_EQ(VpiAssignmentOpType("<<="), vpiLShiftOp);
  EXPECT_EQ(VpiAssignmentOpType(">>="), vpiRShiftOp);
  EXPECT_EQ(VpiAssignmentOpType("<<<="), vpiArithLShiftOp);
  EXPECT_EQ(VpiAssignmentOpType(">>>="), vpiArithRShiftOp);
}

TEST_F(Assignment, AssignmentObjectReportsComputedOpTypeThroughDispatch) {
  VpiObject normal;
  normal.type = vpiAssignment;
  normal.op_type = VpiAssignmentOpType("<=");
  EXPECT_EQ(vpi_get(vpiOpType, VpiHandleOf(&normal)), vpiAssignmentOp);

  VpiObject compound;
  compound.type = vpiAssignment;
  compound.op_type = VpiAssignmentOpType("+=");
  EXPECT_EQ(vpi_get(vpiOpType, VpiHandleOf(&compound)), vpiAddOp);
}

TEST_F(Assignment, UnrecognizedOperatorSpellingFallsBackToVpiAssignmentOp) {
  EXPECT_EQ(VpiAssignmentOpType("=="), vpiAssignmentOp);

  VpiObject fallback;
  fallback.type = vpiAssignment;
  fallback.op_type = VpiAssignmentOpType("==");
  EXPECT_EQ(vpi_get(vpiOpType, VpiHandleOf(&fallback)), vpiAssignmentOp);
}

class AssignmentsOfARun : public VpiDesignRun {
 protected:
  static vpiHandle BodyOf(const std::string& scope) {
    vpiHandle it = vpi_iterate(vpiProcess, By(scope));
    return it == nullptr ? nullptr : vpi_handle(vpiStmt, vpi_scan(it));
  }

  static int IntOf(vpiHandle obj) {
    s_vpi_value value = {};
    value.format = vpiIntVal;
    vpi_get_value(obj, &value);
    return value.value.integer;
  }
};

TEST_F(AssignmentsOfARun, AnIncrementOrDecrementIsAnAssignment) {
  Run("module top; int i, j;\n"
      "  initial begin i++; j--; ++i; --j; end\n"
      "endmodule\n");
  vpiHandle block = BodyOf("top");
  ASSERT_NE(block, nullptr);
  vpiHandle it = vpi_iterate(vpiStmt, block);
  ASSERT_NE(it, nullptr);
  const std::array<int, 4> kOps = {vpiPostIncOp, vpiPostDecOp, vpiPreIncOp,
                                   vpiPreDecOp};
  const std::array<const char*, 4> kTargets = {"top.i", "top.j", "top.i",
                                               "top.j"};
  for (std::size_t k = 0; k < kOps.size(); ++k) {
    vpiHandle step = vpi_scan(it);
    ASSERT_NE(step, nullptr);
    EXPECT_EQ(vpi_get(vpiType, step), vpiAssignment);
    EXPECT_EQ(vpi_get(vpiOpType, step), kOps[k]);
    EXPECT_EQ(vpi_get(vpiBlocking, step), 1);
    EXPECT_EQ(VpiObjectOf(vpi_handle(vpiLhs, step)),
              VpiObjectOf(By(kTargets[k])));
    EXPECT_EQ(vpi_handle(vpiRhs, step), nullptr);
  }
}

TEST_F(AssignmentsOfARun, ABlockingAssignmentIsAnObjectOfTheRun) {
  Run("module top; int a, b; initial a = b; endmodule\n");
  vpiHandle assign = BodyOf("top");
  ASSERT_NE(assign, nullptr);
  EXPECT_EQ(vpi_get(vpiType, assign), vpiAssignment);
  EXPECT_EQ(VpiObjectOf(vpi_handle(vpiLhs, assign)), VpiObjectOf(By("top.a")));
  EXPECT_EQ(VpiObjectOf(vpi_handle(vpiRhs, assign)), VpiObjectOf(By("top.b")));
  EXPECT_EQ(vpi_get(vpiOpType, assign), vpiAssignmentOp);
  EXPECT_EQ(vpi_get(vpiBlocking, assign), 1);
  EXPECT_EQ(VpiObjectOf(vpi_handle(vpiScope, assign)), VpiObjectOf(By("top")));
}

TEST_F(AssignmentsOfARun, ANonblockingAssignmentDoesNotBlock) {
  Run("module top; int a; initial a <= 7; endmodule\n");
  vpiHandle assign = BodyOf("top");
  ASSERT_NE(assign, nullptr);
  EXPECT_EQ(vpi_get(vpiBlocking, assign), 0);
  EXPECT_EQ(vpi_get(vpiOpType, assign), vpiAssignmentOp);
  vpiHandle rhs = vpi_handle(vpiRhs, assign);
  ASSERT_NE(rhs, nullptr);
  EXPECT_EQ(vpi_get(vpiType, rhs), vpiConstant);
  EXPECT_EQ(IntOf(rhs), 7);
}

TEST_F(AssignmentsOfARun, AnAssignmentOperatorReportsItsOperator) {
  Run("module top; int a;\n"
      "  initial a += 2;\n"
      "  initial a <<<= 3;\n"
      "  initial a = a + 2;\n"
      "endmodule\n");
  vpiHandle it = vpi_iterate(vpiProcess, By("top"));
  ASSERT_NE(it, nullptr);
  vpiHandle add = vpi_handle(vpiStmt, vpi_scan(it));
  vpiHandle shift = vpi_handle(vpiStmt, vpi_scan(it));
  vpiHandle written = vpi_handle(vpiStmt, vpi_scan(it));
  ASSERT_NE(add, nullptr);
  ASSERT_NE(shift, nullptr);
  ASSERT_NE(written, nullptr);
  EXPECT_EQ(vpi_get(vpiOpType, add), vpiAddOp);
  EXPECT_EQ(vpi_get(vpiBlocking, add), 1);
  EXPECT_EQ(IntOf(vpi_handle(vpiRhs, add)), 2);
  EXPECT_EQ(vpi_get(vpiOpType, shift), vpiArithLShiftOp);
  EXPECT_EQ(vpi_get(vpiOpType, written), vpiAssignmentOp);
  vpiHandle rhs = vpi_handle(vpiRhs, written);
  ASSERT_NE(rhs, nullptr);
  EXPECT_EQ(vpi_get(vpiType, rhs), vpiOperation);
  EXPECT_EQ(vpi_get(vpiOpType, rhs), vpiAddOp);
}

TEST_F(AssignmentsOfARun, AnIntraAssignmentDelayIsADelayControl) {
  Run("module top; int a, b; initial a = #5 b; endmodule\n");
  vpiHandle assign = BodyOf("top");
  ASSERT_NE(assign, nullptr);
  vpiHandle delay = vpi_handle(vpiDelayControl, assign);
  ASSERT_NE(delay, nullptr);
  EXPECT_EQ(IntOf(vpi_handle(vpiDelay, delay)), 5);
  EXPECT_EQ(vpi_handle(vpiStmt, delay), nullptr);
  EXPECT_EQ(VpiObjectOf(vpi_handle(vpiRhs, assign)), VpiObjectOf(By("top.b")));
  EXPECT_EQ(vpi_handle(vpiEventControl, assign), nullptr);
}

TEST_F(AssignmentsOfARun, AnIntraAssignmentEventIsAnEventControl) {
  Run("module top; bit c; int a, b; initial a <= @(posedge c) b; endmodule\n");
  vpiHandle assign = BodyOf("top");
  ASSERT_NE(assign, nullptr);
  vpiHandle control = vpi_handle(vpiEventControl, assign);
  ASSERT_NE(control, nullptr);
  vpiHandle condition = vpi_handle(vpiCondition, control);
  ASSERT_NE(condition, nullptr);
  EXPECT_EQ(vpi_get(vpiOpType, condition), vpiPosedgeOp);
  vpiHandle operands = vpi_iterate(vpiOperand, condition);
  ASSERT_NE(operands, nullptr);
  EXPECT_EQ(VpiObjectOf(vpi_scan(operands)), VpiObjectOf(By("top.c")));
  EXPECT_EQ(vpi_handle(vpiStmt, control), nullptr);
}

TEST_F(AssignmentsOfARun, AnIntraAssignmentRepeatIsARepeatControl) {
  Run("module top; bit c; int a, b; initial a = repeat (3) @(c) b; "
      "endmodule\n");
  vpiHandle assign = BodyOf("top");
  ASSERT_NE(assign, nullptr);
  vpiHandle repeat = vpi_handle(vpiRepeatControl, assign);
  ASSERT_NE(repeat, nullptr);
  EXPECT_EQ(IntOf(vpi_handle(vpiExpr, repeat)), 3);
  vpiHandle control = vpi_handle(vpiEventControl, repeat);
  ASSERT_NE(control, nullptr);
  EXPECT_EQ(VpiObjectOf(vpi_handle(vpiCondition, control)),
            VpiObjectOf(By("top.c")));
}

TEST_F(AssignmentsOfARun, AnAssignmentReachesTheVariableItsBlockDeclares) {
  Run("module top; int v, w;\n"
      "  initial begin : b int v; begin v = w; end end\n"
      "endmodule\n");
  vpiHandle b = By("top.b");
  ASSERT_NE(b, nullptr);
  vpiHandle it = vpi_iterate(vpiStmt, b);
  ASSERT_NE(it, nullptr);
  vpiHandle inner = vpi_scan(it);
  ASSERT_NE(inner, nullptr);
  vpiHandle stmts = vpi_iterate(vpiStmt, inner);
  ASSERT_NE(stmts, nullptr);
  vpiHandle assign = vpi_scan(stmts);
  ASSERT_NE(assign, nullptr);
  EXPECT_EQ(VpiObjectOf(vpi_handle(vpiLhs, assign)),
            VpiObjectOf(By("top.b.v")));
  EXPECT_EQ(VpiObjectOf(vpi_handle(vpiRhs, assign)), VpiObjectOf(By("top.w")));
}

TEST_F(AssignmentsOfARun, AnAssignmentInAGenerateBlockReachesItsVariable) {
  Run("module top; logic v;\n"
      "  for (genvar i = 0; i < 2; i++) begin : g logic v; initial v = 1; end\n"
      "endmodule\n");
  vpiHandle assign = BodyOf("top.g[1]");
  ASSERT_NE(assign, nullptr);
  vpiHandle lhs = vpi_handle(vpiLhs, assign);
  ASSERT_NE(lhs, nullptr);
  EXPECT_NE(VpiObjectOf(lhs), VpiObjectOf(By("top.v")));
  EXPECT_EQ(VpiObjectOf(lhs), VpiObjectOf(By("top.g[1].v")));
  EXPECT_STREQ(vpi_get_str(vpiName, lhs), "v");
}

}  // namespace
}  // namespace delta
