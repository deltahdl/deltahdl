#include <gtest/gtest.h>

#include "common/types.h"
#include "fixture_vpi_run.h"
#include "simulator/sv_vpi_user.h"
#include "simulator/variable.h"
#include "simulator/vpi_context.h"
#include "simulator/vpi_globals.h"
#include "simulator/vpi_model_helpers1.h"
#include "simulator/vpi_object.h"
#include "simulator/vpi_user.h"

namespace delta {
namespace {

class DelayControl : public ::testing::Test {
 protected:
  void SetUp() override { SetGlobalVpiContext(&ctx_); }
  void TearDown() override { SetGlobalVpiContext(nullptr); }
  VpiContext ctx_;
};

TEST_F(DelayControl, StandaloneDelayControlReachesItsStatement) {
  VpiObject stmt;
  stmt.type = vpiBegin;

  VpiObject delay_control;
  delay_control.type = vpiDelayControl;
  delay_control.children = {&stmt};

  EXPECT_EQ(VpiDelayControlStmt(&delay_control), &stmt);

  VpiObject host_stmt;
  host_stmt.type = vpiBegin;
  delay_control.parent = &host_stmt;
  EXPECT_EQ(VpiDelayControlStmt(&delay_control), &stmt);
}

TEST_F(DelayControl, NullAndEmptyDelayControlsReportNoStatement) {
  EXPECT_EQ(VpiDelayControlStmt(nullptr), nullptr);

  VpiObject bare;
  bare.type = vpiDelayControl;
  EXPECT_EQ(VpiDelayControlStmt(&bare), nullptr);
}

TEST_F(DelayControl, RuleAppliesThroughPublicVpiHandleDispatch) {
  VpiObject guarded;
  guarded.type = vpiBegin;

  VpiObject assignment;
  assignment.type = vpiAssignment;

  VpiObject on_assignment;
  on_assignment.type = vpiDelayControl;
  on_assignment.parent = &assignment;
  on_assignment.children = {&guarded};
  EXPECT_EQ(vpi_handle(vpiStmt, VpiHandleOf(&on_assignment)), nullptr);

  VpiObject standalone;
  standalone.type = vpiDelayControl;
  standalone.children = {&guarded};
  EXPECT_EQ(VpiObjectOf(vpi_handle(vpiStmt, VpiHandleOf(&standalone))),
            &guarded);
}

TEST_F(DelayControl, DelayControlReachesItsDelayExpressionThroughVpiDelay) {
  VpiObject delay_expr;
  delay_expr.type = vpiConstant;

  VpiObject guarded;
  guarded.type = vpiBegin;

  VpiObject delay_control;
  delay_control.type = vpiDelayControl;
  delay_control.children = {&guarded, &delay_expr};

  EXPECT_EQ(VpiObjectOf(vpi_handle(vpiDelay, VpiHandleOf(&delay_control))),
            &delay_expr);
  EXPECT_EQ(VpiDelayControlDelayExpr(&delay_control), &delay_expr);
}

TEST_F(DelayControl, IntraAssignmentDelayStillReachesItsDelayExpression) {
  VpiObject delay_expr;
  delay_expr.type = vpiRefObj;

  VpiObject assignment;
  assignment.type = vpiAssignment;

  VpiObject on_assignment;
  on_assignment.type = vpiDelayControl;
  on_assignment.parent = &assignment;
  on_assignment.children = {&delay_expr};

  EXPECT_EQ(vpi_handle(vpiStmt, VpiHandleOf(&on_assignment)), nullptr);
  EXPECT_EQ(VpiObjectOf(vpi_handle(vpiDelay, VpiHandleOf(&on_assignment))),
            &delay_expr);
}

TEST_F(DelayControl, NullAndDelaylessControlsReportNoDelayExpression) {
  EXPECT_EQ(VpiDelayControlDelayExpr(nullptr), nullptr);

  VpiObject only_stmt;
  only_stmt.type = vpiDelayControl;
  VpiObject guarded;
  guarded.type = vpiBegin;
  only_stmt.children = {&guarded};
  EXPECT_EQ(VpiDelayControlDelayExpr(&only_stmt), nullptr);
}

TEST_F(DelayControl, ComputedDelayExpressionReachedThroughVpiDelay) {
  VpiObject delay_expr;
  delay_expr.type = vpiOperation;

  VpiObject delay_control;
  delay_control.type = vpiDelayControl;
  delay_control.children = {&delay_expr};

  EXPECT_EQ(VpiObjectOf(vpi_handle(vpiDelay, VpiHandleOf(&delay_control))),
            &delay_expr);
  EXPECT_EQ(VpiDelayControlDelayExpr(&delay_control), &delay_expr);
}

TEST_F(DelayControl, StatementScanSkipsDelayExpressionChild) {
  VpiObject delay_expr;
  delay_expr.type = vpiConstant;

  VpiObject delay_control;
  delay_control.type = vpiDelayControl;
  delay_control.children = {&delay_expr};

  EXPECT_EQ(vpi_handle(vpiStmt, VpiHandleOf(&delay_control)), nullptr);
  EXPECT_EQ(VpiDelayControlStmt(&delay_control), nullptr);
}

TEST_F(DelayControl, ADelayControlWithNoDelayExpressionGivesAZeroDelay) {
  VpiObject guarded;
  guarded.type = vpiNullStmt;
  VpiObject delay_control;
  delay_control.type = vpiDelayControl;
  delay_control.children = {&guarded};

  s_vpi_time slot = {};
  slot.low = 7;
  s_vpi_delay delay = {};
  delay.da = &slot;
  delay.no_of_delays = 1;
  delay.time_type = vpiSimTime;
  vpi_get_delays(VpiHandleOf(&delay_control), &delay);
  EXPECT_EQ(ctx_.LastError().level, 0);
  EXPECT_EQ(slot.type, vpiSimTime);
  EXPECT_EQ(slot.low, 0U);
}

TEST_F(DelayControl, AMinTypMaxDelayShortOfAnOperandGivesItsWholeValue) {
  Logic4Word nine{9, 0};
  Variable held{};
  held.value.width = 32;
  held.value.nwords = 1;
  held.value.words = &nine;
  VpiObject typ;
  typ.type = vpiConstant;
  typ.var = &held;
  VpiObject max;
  max.type = vpiConstant;
  VpiObject min_typ_max;
  min_typ_max.type = vpiOperation;
  min_typ_max.op_type = vpiMinTypMaxOp;
  min_typ_max.children = {&typ, &max};
  VpiObject delay_control;
  delay_control.type = vpiDelayControl;
  delay_control.children = {&min_typ_max};

  s_vpi_time slots[3] = {};
  for (s_vpi_time& slot : slots) slot.low = 7;
  s_vpi_delay delay = {};
  delay.da = slots;
  delay.no_of_delays = 1;
  delay.time_type = vpiSimTime;
  delay.mtm_flag = 1;
  vpi_get_delays(VpiHandleOf(&delay_control), &delay);
  for (const s_vpi_time& slot : slots) EXPECT_EQ(slot.low, 0U);
}

class DelayControlsOfARun : public VpiDesignRun {
 protected:
  static vpiHandle Control() {
    vpiHandle procs = vpi_iterate(vpiProcess, By("top"));
    if (procs == nullptr) return nullptr;
    vpiHandle control = vpi_handle(vpiStmt, vpi_scan(procs));
    if (control != nullptr)
      EXPECT_EQ(vpi_get(vpiType, control), vpiDelayControl);
    return control;
  }
};

TEST_F(DelayControlsOfARun, ADelayControlIsAnObjectOfTheRun) {
  Run("module top; int a; initial #5 a = 1; endmodule\n");
  vpiHandle control = Control();
  ASSERT_NE(control, nullptr);
  vpiHandle delay = vpi_handle(vpiDelay, control);
  ASSERT_NE(delay, nullptr);
  EXPECT_EQ(vpi_get(vpiType, delay), vpiConstant);
  s_vpi_value value = {};
  value.format = vpiIntVal;
  vpi_get_value(delay, &value);
  EXPECT_EQ(value.value.integer, 5);
  vpiHandle delayed = vpi_handle(vpiStmt, control);
  ASSERT_NE(delayed, nullptr);
  EXPECT_EQ(vpi_get(vpiType, delayed), vpiAssignment);
  EXPECT_EQ(VpiObjectOf(vpi_handle(vpiLhs, delayed)), VpiObjectOf(By("top.a")));
}

TEST_F(DelayControlsOfARun, ADelayWrittenAsANameIsWhatItNames) {
  Run("module top; int d = 2; initial #d ; endmodule\n");
  vpiHandle control = Control();
  ASSERT_NE(control, nullptr);
  EXPECT_EQ(VpiObjectOf(vpi_handle(vpiDelay, control)),
            VpiObjectOf(By("top.d")));
  vpiHandle delayed = vpi_handle(vpiStmt, control);
  ASSERT_NE(delayed, nullptr);
  EXPECT_EQ(vpi_get(vpiType, delayed), vpiNullStmt);
}

TEST_F(DelayControlsOfARun, ADelayControlGivesItsDelayThroughGetDelays) {
  Run("module top; timeunit 1ns; timeprecision 1ps;\n"
      "  int a; initial #5 a = 1;\n"
      "endmodule\n");
  vpiHandle control = Control();
  ASSERT_NE(control, nullptr);
  s_vpi_time slot = {};
  s_vpi_delay delay = {};
  delay.da = &slot;
  delay.no_of_delays = 1;
  delay.time_type = vpiSimTime;
  vpi_get_delays(control, &delay);
  EXPECT_EQ(slot.type, vpiSimTime);
  EXPECT_EQ(slot.high, 0U);
  EXPECT_EQ(slot.low, 5000U);
}

TEST_F(DelayControlsOfARun, AComputedDelayGivesItsValueAsEachOfTheThree) {
  Run("module top; timeunit 1ns; timeprecision 1ns;\n"
      "  int d = 2; int a; initial #(d + 1) a = 1;\n"
      "endmodule\n");
  vpiHandle control = Control();
  ASSERT_NE(control, nullptr);
  ASSERT_EQ(vpi_get(vpiOpType, vpi_handle(vpiDelay, control)), vpiAddOp);
  s_vpi_time slots[3] = {};
  s_vpi_delay delay = {};
  delay.da = slots;
  delay.no_of_delays = 1;
  delay.time_type = vpiSimTime;
  delay.mtm_flag = 1;
  vpi_get_delays(control, &delay);
  for (const s_vpi_time& slot : slots) EXPECT_EQ(slot.low, 3U);
}

}  // namespace
}  // namespace delta
