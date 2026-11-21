#include <gtest/gtest.h>

#include <string>
#include <vector>

#include "fixture_vpi_run.h"
#include "simulator/vpi_constants.h"
#include "simulator/vpi_context.h"
#include "simulator/vpi_globals.h"
#include "simulator/vpi_internal.h"
#include "simulator/vpi_model_helpers1.h"
#include "simulator/vpi_object.h"
#include "simulator/vpi_user.h"

namespace delta {
namespace {

class ContinuousAssignment : public ::testing::Test {
 protected:
  void SetUp() override { SetGlobalVpiContext(&ctx_); }
  void TearDown() override { SetGlobalVpiContext(nullptr); }
  VpiContext ctx_;
};

TEST_F(ContinuousAssignment, ContAssignBitSizeIsAlwaysScalar) {
  VpiObject bit;
  bit.type = vpiContAssignBit;
  bit.size = 8;
  EXPECT_EQ(vpi_get(vpiSize, VpiHandleOf(&bit)), 1);

  VpiObject assign;
  assign.type = vpiContAssign;
  assign.size = 4;
  EXPECT_EQ(vpi_get(vpiSize, VpiHandleOf(&assign)), 4);
}

TEST_F(ContinuousAssignment, LsbContAssignBitReportsZeroOffset) {
  VpiObject lsb;
  lsb.type = vpiContAssignBit;
  lsb.offset = 0;
  EXPECT_EQ(vpi_get(vpiOffset, VpiHandleOf(&lsb)), 0);

  VpiObject higher;
  higher.type = vpiContAssignBit;
  higher.offset = 3;
  EXPECT_EQ(vpi_get(vpiOffset, VpiHandleOf(&higher)), 3);
}

TEST_F(ContinuousAssignment, ReportsNetDeclAssign) {
  VpiObject net_decl;
  net_decl.type = vpiContAssign;
  net_decl.net_decl_assign = true;
  EXPECT_EQ(vpi_get(vpiNetDeclAssign, VpiHandleOf(&net_decl)), 1);

  VpiObject standalone;
  standalone.type = vpiContAssign;
  EXPECT_EQ(vpi_get(vpiNetDeclAssign, VpiHandleOf(&standalone)), 0);
}

TEST_F(ContinuousAssignment, ReportsDriveStrengths) {
  VpiObject assign;
  assign.type = vpiContAssign;
  assign.strength0 = vpiPullDrive;
  assign.strength1 = vpiStrongDrive;
  EXPECT_EQ(vpi_get(vpiStrength0, VpiHandleOf(&assign)), vpiPullDrive);
  EXPECT_EQ(vpi_get(vpiStrength1, VpiHandleOf(&assign)), vpiStrongDrive);
}

TEST_F(ContinuousAssignment, ValueChangeCallbackAllowedOnContAssignAndBit) {
  VpiObject assign;
  assign.type = vpiContAssign;
  s_cb_data on_assign = {};
  on_assign.reason = cbValueChange;
  on_assign.obj = VpiHandleOf(&assign);
  EXPECT_NE(ctx_.RegisterCb(&on_assign), nullptr);

  VpiObject bit;
  bit.type = vpiContAssignBit;
  s_cb_data on_bit = {};
  on_bit.reason = cbValueChange;
  on_bit.obj = VpiHandleOf(&bit);
  EXPECT_NE(ctx_.RegisterCb(&on_bit), nullptr);
}

TEST_F(ContinuousAssignment, AContinuousAssignmentReachesItsTwoSides) {
  VpiObject target;
  target.type = kVpiNet;
  VpiObject source;
  source.type = vpiOperation;

  VpiObject assign;
  assign.type = vpiContAssign;
  assign.lhs = &target;
  assign.rhs = &source;

  EXPECT_EQ(VpiObjectOf(vpi_handle(vpiLhs, VpiHandleOf(&assign))), &target);
  EXPECT_EQ(VpiObjectOf(vpi_handle(vpiRhs, VpiHandleOf(&assign))), &source);
}

TEST_F(ContinuousAssignment, AContAssignBitReachesTheSameTwoSides) {
  VpiObject target;
  target.type = vpiNetBit;
  VpiObject source;
  source.type = vpiConstant;

  VpiObject bit;
  bit.type = vpiContAssignBit;
  bit.lhs = &target;
  bit.rhs = &source;

  EXPECT_EQ(VpiObjectOf(vpi_handle(vpiLhs, VpiHandleOf(&bit))), &target);
  EXPECT_EQ(VpiObjectOf(vpi_handle(vpiRhs, VpiHandleOf(&bit))), &source);
}

TEST_F(ContinuousAssignment, AContAssignBitReachesItsSourceDelay) {
  EXPECT_TRUE(VpiObjectCarriesSourceDelay(vpiContAssign));
  EXPECT_TRUE(VpiObjectCarriesSourceDelay(vpiContAssignBit));

  VpiObject delay_expr;
  delay_expr.type = vpiConstant;

  VpiObject bit;
  bit.type = vpiContAssignBit;
  bit.delay_expr = &delay_expr;

  EXPECT_EQ(VpiObjectOf(vpi_handle(vpiDelay, VpiHandleOf(&bit))), &delay_expr);
}

TEST_F(ContinuousAssignment, TheEdgesStayDistinctAndReportNoneWhenAbsent) {
  VpiObject target;
  target.type = kVpiNet;

  VpiObject assign;
  assign.type = vpiContAssign;
  assign.lhs = &target;

  EXPECT_EQ(VpiObjectOf(vpi_handle(vpiLhs, VpiHandleOf(&assign))), &target);
  EXPECT_EQ(vpi_handle(vpiRhs, VpiHandleOf(&assign)), nullptr);
  EXPECT_EQ(vpi_handle(vpiDelay, VpiHandleOf(&assign)), nullptr);
}

int g_assign_changes = 0;
int g_bit_changes = 0;
vpiHandle g_assign_callback = nullptr;
vpiHandle g_bit_callback = nullptr;

PLI_INT32 CountAssignChange(p_cb_data) {
  ++g_assign_changes;
  return 0;
}

PLI_INT32 CountBitChange(p_cb_data) {
  ++g_bit_changes;
  return 0;
}

PLI_INT32 UnwatchBitCalltf(PLI_BYTE8*) {
  vpi_remove_cb(g_bit_callback);
  return 0;
}

vpiHandle FirstAssignOfTop() {
  vpiHandle it =
      vpi_iterate(vpiContAssign, vpi_handle_by_name(VpiText("top"), nullptr));
  vpiHandle assign = it == nullptr ? nullptr : vpi_scan(it);
  if (assign != nullptr) vpi_release_handle(it);
  return assign;
}

vpiHandle PlaceValueChange(vpiHandle obj, PLI_INT32 (*routine)(p_cb_data)) {
  s_cb_data cb = {};
  cb.reason = cbValueChange;
  cb.obj = obj;
  cb.cb_rtn = routine;
  return vpi_register_cb(&cb);
}

PLI_INT32 WatchAssignCalltf(PLI_BYTE8*) {
  vpiHandle assign = FirstAssignOfTop();
  if (assign == nullptr) return 0;
  g_assign_callback = PlaceValueChange(assign, &CountAssignChange);
  vpiHandle bits = vpi_iterate(vpiBit, assign);
  while (vpiHandle bit = bits == nullptr ? nullptr : vpi_scan(bits)) {
    if (vpi_get(vpiOffset, bit) != 3) continue;
    g_bit_callback = PlaceValueChange(bit, &CountBitChange);
  }
  return 0;
}

PLI_INT32 WatchAssignTwiceCalltf(PLI_BYTE8*) {
  vpiHandle assign = FirstAssignOfTop();
  if (assign == nullptr) return 0;
  PlaceValueChange(assign, &CountAssignChange);
  PlaceValueChange(assign, &CountAssignChange);
  return 0;
}

class ContinuousAssignmentsOfARun : public VpiDesignRun {
 protected:
  static void RegisterTask(const char* name, PLI_INT32 (*calltf)(PLI_BYTE8*)) {
    s_vpi_systf_data data = {};
    data.type = vpiSysTask;
    data.tfname = VpiText(name);
    data.calltf = calltf;
    ASSERT_NE(vpi_register_systf(&data), nullptr);
  }

  static int CountOf(int type, vpiHandle ref) {
    int count = 0;
    vpiHandle it = vpi_iterate(type, ref);
    if (it == nullptr) return 0;
    while (vpi_scan(it) != nullptr) ++count;
    return count;
  }

  static vpiHandle AssignStatementOfTop() {
    vpiHandle it =
        vpi_iterate(vpiContAssign, vpi_handle_by_name(VpiText("top"), nullptr));
    if (it == nullptr) return nullptr;
    vpiHandle found = nullptr;
    while (vpiHandle ca = vpi_scan(it)) {
      if (vpi_get(vpiNetDeclAssign, ca) == 0) found = ca;
    }
    return found;
  }
};

int IntValueOf(vpiHandle obj) {
  s_vpi_value value = {};
  value.format = vpiIntVal;
  vpi_get_value(obj, &value);
  return value.value.integer;
}

constexpr const char* kVectorAssignment =
    "module top; logic [3:0] a, b; wire [3:0] y;\n"
    "  assign y = a ^ b;\n"
    "  initial begin\n"
    "    a = 4'b0011; b = 4'b0101; $watchca;\n"
    "    #5 a = 4'b1111; #5 a = 4'b1111; $unwatchbit; #5 a = 4'b0000;\n"
    "  end\n"
    "endmodule\n";

constexpr const char* kTwoAssignments =
    "module top;\n"
    "  wire a, b, y;\n"
    "  wire w = a;\n"
    "  assign y = a & b;\n"
    "endmodule\n";

TEST_F(ContinuousAssignmentsOfARun, AModuleReachesItsContinuousAssignments) {
  Run(kTwoAssignments);
  EXPECT_EQ(CountOf(vpiContAssign, vpi_handle_by_name(VpiText("top"), nullptr)),
            2);
}

TEST_F(ContinuousAssignmentsOfARun, ItsLeftHandSideIsTheNetItDrives) {
  Run(kTwoAssignments);
  vpiHandle ca = AssignStatementOfTop();
  ASSERT_NE(ca, nullptr);
  EXPECT_STREQ(vpi_get_str(vpiName, vpi_handle(vpiLhs, ca)), "y");
}

TEST_F(ContinuousAssignmentsOfARun, ItsRightHandSideIsAnOperation) {
  Run(kTwoAssignments);
  vpiHandle ca = AssignStatementOfTop();
  ASSERT_NE(ca, nullptr);
  EXPECT_EQ(vpi_get(vpiType, vpi_handle(vpiRhs, ca)), vpiOperation);
}

TEST_F(ContinuousAssignmentsOfARun, TheOperationHasTheSourcesOperator) {
  Run(kTwoAssignments);
  vpiHandle ca = AssignStatementOfTop();
  ASSERT_NE(ca, nullptr);
  EXPECT_EQ(vpi_get(vpiOpType, vpi_handle(vpiRhs, ca)), vpiBitAndOp);
}

TEST_F(ContinuousAssignmentsOfARun, TheOperationsOperandsAreTheNetsItReads) {
  Run(kTwoAssignments);
  vpiHandle ca = AssignStatementOfTop();
  ASSERT_NE(ca, nullptr);
  EXPECT_EQ(NamesOf(vpiOperand, vpi_handle(vpiRhs, ca)),
            (std::vector<std::string>{"a", "b"}));
}

TEST_F(ContinuousAssignmentsOfARun, ANetDeclarationsAssignmentIsMarked) {
  Run(kTwoAssignments);
  vpiHandle it =
      vpi_iterate(vpiContAssign, vpi_handle_by_name(VpiText("top"), nullptr));
  ASSERT_NE(it, nullptr);
  int marked = 0;
  while (vpiHandle ca = vpi_scan(it)) marked += vpi_get(vpiNetDeclAssign, ca);
  EXPECT_EQ(marked, 1);
}

TEST_F(ContinuousAssignmentsOfARun, ItDrivesTheNetOnItsLeft) {
  Run(kTwoAssignments);
  EXPECT_EQ(CountOf(vpiDriver, vpi_handle_by_name(VpiText("top.y"), nullptr)),
            1);
}

TEST_F(ContinuousAssignmentsOfARun, ItLoadsEachNetItReads) {
  Run(kTwoAssignments);
  EXPECT_EQ(CountOf(vpiLoad, vpi_handle_by_name(VpiText("top.a"), nullptr)), 2);
}

TEST_F(ContinuousAssignmentsOfARun, AnAssignmentToAConcatenationIsOneObject) {
  Run("module top; wire [1:0] r; wire p, q; assign {p, q} = r; endmodule\n");
  EXPECT_EQ(CountOf(vpiContAssign, vpi_handle_by_name(VpiText("top"), nullptr)),
            1);
}

TEST_F(ContinuousAssignmentsOfARun, AnAssignmentToAConcatenationDrivesEach) {
  Run("module top; wire [1:0] r; wire p, q; assign {p, q} = r; endmodule\n");
  EXPECT_EQ(CountOf(vpiDriver, vpi_handle_by_name(VpiText("top.q"), nullptr)),
            1);
}

TEST_F(ContinuousAssignmentsOfARun, AnInstanceReachesItsOwnAssignments) {
  Run("module sub(input c, output d); assign d = ~c; endmodule\n"
      "module top; wire x, z; sub u(.c(x), .d(z)); endmodule\n");
  EXPECT_EQ(
      CountOf(vpiContAssign, vpi_handle_by_name(VpiText("top.u"), nullptr)), 1);
}

TEST_F(ContinuousAssignmentsOfARun,
       EachGenerateBlockInstanceHoldsItsAssignment) {
  Run("module top; wire [1:0] a;\n"
      "  for (genvar g = 0; g < 2; g++) begin : gb\n"
      "    wire y; assign y = a[g];\n"
      "  end\n"
      "endmodule\n");
  EXPECT_EQ(CountOf(vpiContAssign, vpi_handle_by_name(VpiText("top"), nullptr)),
            0);
  for (const char* scope : {"top.gb[0]", "top.gb[1]"}) {
    EXPECT_EQ(
        CountOf(vpiContAssign, vpi_handle_by_name(VpiText(scope), nullptr)), 1);
  }
  EXPECT_EQ(
      CountOf(vpiDriver, vpi_handle_by_name(VpiText("top.gb[1].y"), nullptr)),
      1);
}

TEST_F(ContinuousAssignmentsOfARun, AVectorAssignmentHasAValueAndBits) {
  g_assign_changes = 0;
  g_bit_changes = 0;
  RegisterTask("$watchca", &WatchAssignCalltf);
  RegisterTask("$unwatchbit", &UnwatchBitCalltf);
  Run(kVectorAssignment);
  vpiHandle assign = AssignStatementOfTop();
  ASSERT_NE(assign, nullptr);
  EXPECT_EQ(IntValueOf(assign), 0b0101);
  std::vector<vpiHandle> bits;
  vpiHandle it = vpi_iterate(vpiBit, assign);
  ASSERT_NE(it, nullptr);
  while (vpiHandle bit = vpi_scan(it)) bits.push_back(bit);
  ASSERT_EQ(bits.size(), 4U);
  for (vpiHandle bit : bits) {
    EXPECT_EQ(vpi_get(vpiType, bit), vpiContAssignBit);
    EXPECT_EQ(vpi_get(vpiSize, bit), 1);
    EXPECT_EQ(VpiObjectOf(vpi_handle(vpiParent, bit)), VpiObjectOf(assign));
    const int kOffset = vpi_get(vpiOffset, bit);
    EXPECT_EQ(IntValueOf(bit), (0b0101 >> kOffset) & 1) << kOffset;
  }
  EXPECT_EQ(g_assign_changes, 2);
  EXPECT_EQ(g_bit_changes, 1);
}

TEST_F(ContinuousAssignmentsOfARun, AnAssignmentsValueHasItsLeftSidesWidth) {
  Run("module top; logic [3:0] a = 4'hF, b = 4'h1, c = 4'hE;\n"
      "  wire [7:0] y; wire [2:0] z;\n"
      "  assign y = a + b;\n"
      "  assign z = c + b;\n"
      "endmodule\n");
  vpiHandle y = nullptr;
  vpiHandle z = nullptr;
  vpiHandle it =
      vpi_iterate(vpiContAssign, vpi_handle_by_name(VpiText("top"), nullptr));
  ASSERT_NE(it, nullptr);
  while (vpiHandle assign = vpi_scan(it)) {
    const std::string kLhs = vpi_get_str(vpiName, vpi_handle(vpiLhs, assign));
    if (kLhs == "y") {
      y = assign;
    } else {
      z = assign;
    }
  }
  ASSERT_NE(y, nullptr);
  ASSERT_NE(z, nullptr);
  EXPECT_EQ(IntValueOf(y), 16);
  EXPECT_EQ(IntValueOf(z), 7);
  int high = 0;
  vpiHandle bit_it = vpi_iterate(vpiBit, y);
  ASSERT_NE(bit_it, nullptr);
  while (vpiHandle bit = vpi_scan(bit_it)) {
    const int kOffset = vpi_get(vpiOffset, bit);
    if (kOffset >= 4) high |= IntValueOf(bit) << (kOffset - 4);
  }
  EXPECT_EQ(high, 1);
}

TEST_F(ContinuousAssignmentsOfARun, TwoCallbacksOnOneAssignmentEachCalledOnce) {
  g_assign_changes = 0;
  RegisterTask("$watchcatwice", &WatchAssignTwiceCalltf);
  Run("module top; logic [3:0] a; wire [3:0] y;\n"
      "  assign y = ~a;\n"
      "  initial begin\n"
      "    a = 4'b0000; $watchcatwice;\n"
      "    #5 a = 4'b0011; #5 a = 4'b0011;\n"
      "  end\n"
      "endmodule\n");
  EXPECT_EQ(g_assign_changes, 2);
}

TEST_F(ContinuousAssignmentsOfARun, AnAssignmentOfAConstantIsNeverCalledBack) {
  g_assign_changes = 0;
  RegisterTask("$watchca", &WatchAssignCalltf);
  Run("module top; typedef enum logic [1:0] {A, B, C} e_t;\n"
      "  logic [1:0] a; wire [1:0] y;\n"
      "  assign y = C;\n"
      "  initial begin a = 2'b00; $watchca; #5 a = 2'b11; end\n"
      "endmodule\n");
  vpiHandle assign = FirstAssignOfTop();
  ASSERT_NE(assign, nullptr);
  EXPECT_EQ(IntValueOf(assign), 2);
  EXPECT_EQ(g_assign_changes, 0);
}

TEST_F(ContinuousAssignmentsOfARun,
       AnEquivalencesAssignmentIsCalledBackAsItChanges) {
  g_assign_changes = 0;
  g_assign_callback = nullptr;
  RegisterTask("$watchca", &WatchAssignCalltf);
  Run("module top; logic a, b; wire y;\n"
      "  assign y = a <-> b;\n"
      "  initial begin\n"
      "    a = 1'b0; b = 1'b0; $watchca;\n"
      "    #5 a = 1'b1; #5 b = 1'b1; #5 b = 1'b1;\n"
      "  end\n"
      "endmodule\n");
  vpiHandle assign = FirstAssignOfTop();
  ASSERT_NE(assign, nullptr);
  EXPECT_NE(g_assign_callback, nullptr);
  EXPECT_EQ(g_assign_changes, 2);
  EXPECT_EQ(IntValueOf(assign), 1);
}

TEST_F(ContinuousAssignmentsOfARun,
       AStaticPropertysAssignmentIsCalledBackAsItChanges) {
  g_assign_changes = 0;
  RegisterTask("$watchca", &WatchAssignCalltf);
  Run("module top;\n"
      "  class C; static int s; endclass\n"
      "  wire [31:0] y;\n"
      "  assign y = C::s + 1;\n"
      "  initial begin $watchca; #5 C::s = 3; #5 C::s = 3; end\n"
      "endmodule\n");
  EXPECT_EQ(g_assign_changes, 1);
}

}  // namespace
}  // namespace delta
