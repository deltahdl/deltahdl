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

// §37.47 Continuous assignment: the object model diagram draws a "cont assign"
// object (reached from its module, carrying vpiLhs/vpiRhs/vpiDelay expression
// edges and the vpiNetDeclAssign, vpiStrength0/vpiStrength1, delay and value
// properties) and a "cont assign bit" object reached through vpiBit, which
// reports its offset from the LSB through vpiOffset. Three numbered Details add
// the normative rules these tests pin down:
//   1) the size of a cont assign bit is always scalar;
//   2) value change callbacks may be placed onto a cont assign or a cont assign
//      bit;
//   3) vpiOffset shall return zero for the LSB.
// The structural edges and the delay/value reads are descriptive or belong to
// dependency subclauses (vpi_get_delays() is §38.10, the value read §38.34, and
// the value change callback machinery §38.36.1); these tests exercise the
// properties §37.47's own text defines, through the production dispatch in
// vpi.cpp.

// The fixture installs a context so the public vpi_get entry point runs its
// real dispatch and so callbacks register through the same context.
class ContinuousAssignment : public ::testing::Test {
 protected:
  void SetUp() override { SetGlobalVpiContext(&ctx_); }
  void TearDown() override { SetGlobalVpiContext(nullptr); }
  VpiContext ctx_;
};

// Detail 1: a cont assign bit is always scalar - vpi_get(vpiSize) reports one
// even when the object was handed a wider stored size. A non-bit cont assign is
// outside this rule and reports its own stored size, confirming the guard is
// scoped to the bit object.
TEST_F(ContinuousAssignment, ContAssignBitSizeIsAlwaysScalar) {
  VpiObject bit;
  bit.type = vpiContAssignBit;
  bit.size = 8;  // a deliberately non-scalar stored width
  EXPECT_EQ(vpi_get(vpiSize, VpiHandleOf(&bit)), 1);

  VpiObject assign;
  assign.type = vpiContAssign;
  assign.size = 4;
  EXPECT_EQ(vpi_get(vpiSize, VpiHandleOf(&assign)), 4);
}

// Detail 3: vpiOffset shall return zero for the LSB. The offset is measured
// from the least significant bit, so the LSB bit reports zero and a bit three
// positions above it reports three.
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

// Diagram property: a continuous assignment reports through vpiNetDeclAssign
// whether it is a net declaration assignment. An assignment marked as such
// reports TRUE; an ordinary assign statement reports FALSE.
TEST_F(ContinuousAssignment, ReportsNetDeclAssign) {
  VpiObject net_decl;
  net_decl.type = vpiContAssign;
  net_decl.net_decl_assign = true;
  EXPECT_EQ(vpi_get(vpiNetDeclAssign, VpiHandleOf(&net_decl)), 1);

  VpiObject standalone;
  standalone.type = vpiContAssign;
  EXPECT_EQ(vpi_get(vpiNetDeclAssign, VpiHandleOf(&standalone)), 0);
}

// Diagram property: a continuous assignment reports the drive strengths it
// carries on its 0 and 1 values through vpiStrength0 and vpiStrength1.
TEST_F(ContinuousAssignment, ReportsDriveStrengths) {
  VpiObject assign;
  assign.type = vpiContAssign;
  assign.strength0 = vpiPullDrive;
  assign.strength1 = vpiStrongDrive;
  EXPECT_EQ(vpi_get(vpiStrength0, VpiHandleOf(&assign)), vpiPullDrive);
  EXPECT_EQ(vpi_get(vpiStrength1, VpiHandleOf(&assign)), vpiStrongDrive);
}

// Detail 2: a value change callback may be placed onto a cont assign or onto a
// cont assign bit. Neither object kind is rejected by registration, so both
// hand back a live callback handle.
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

// -----------------------------------------------------------------------------
// The edges the enclosure carries. §37.47 draws `cont assign` and `cont assign
// bit` inside one dotted outline with no name, and hangs vpiLhs, vpiRhs and
// vpiDelay off that outline rather than off either object. §37.4.1 makes an
// unnamed enclosure a grouping of the objects drawn in it, so both of them
// carry all three edges. None of the three named a continuous assignment at
// all: vpiLhs and vpiRhs were served for the procedural assignment family and
// the alias statement only, and vpiDelay for the whole assignment but not its
// bits, so the traversal fell through to a match of a child's own type against
// a relation tag, which no object carries.
// -----------------------------------------------------------------------------

// §37.47 (figure, vpiLhs/vpiRhs): a continuous assignment reaches the net it
// drives and the expression it drives it with.
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

// §37.47 (figure): the two edges are drawn on the enclosure, so a cont assign
// bit answers for them exactly as the whole assignment does.
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

// §37.47 (figure, vpiDelay): the delay edge is drawn on the same enclosure, so
// a cont assign bit reaches the source-written delay its assignment does.
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

// §37.47 (figure): an assignment written with no delay reaches none, and the
// edges stay distinct - a target is not reported as a source.
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

// A design run with a PLI application registered, its continuous assignments
// read back once the run is over.
// How many times the value change callbacks $watchca places on top's
// continuous assignment and on that assignment's bit 3 have been called back.
int g_assign_changes = 0;
int g_bit_changes = 0;
vpiHandle g_bit_callback = nullptr;

PLI_INT32 CountAssignChange(p_cb_data /*data*/) {
  ++g_assign_changes;
  return 0;
}

PLI_INT32 CountBitChange(p_cb_data /*data*/) {
  ++g_bit_changes;
  return 0;
}

// $unwatchbit: take the callback on the bit away, so a later change of the
// assignment finds none placed on the bit.
PLI_INT32 UnwatchBitCalltf(PLI_BYTE8* /*user_data*/) {
  vpi_remove_cb(g_bit_callback);
  return 0;
}

// $watchca: place a value change callback on the first continuous assignment
// top reaches and one on its bit at offset 3.
PLI_INT32 WatchAssignCalltf(PLI_BYTE8* /*user_data*/) {
  vpiHandle it =
      vpi_iterate(vpiContAssign, vpi_handle_by_name(VpiText("top"), nullptr));
  vpiHandle assign = it == nullptr ? nullptr : vpi_scan(it);
  if (assign == nullptr) return 0;
  vpi_release_handle(it);
  s_cb_data cb = {};
  cb.reason = cbValueChange;
  cb.obj = assign;
  cb.cb_rtn = &CountAssignChange;
  vpi_register_cb(&cb);
  vpiHandle bits = vpi_iterate(vpiBit, assign);
  while (vpiHandle bit = bits == nullptr ? nullptr : vpi_scan(bits)) {
    if (vpi_get(vpiOffset, bit) != 3) continue;
    cb.obj = bit;
    cb.cb_rtn = &CountBitChange;
    g_bit_callback = vpi_register_cb(&cb);
  }
  return 0;
}

class ContinuousAssignmentsOfARun : public VpiDesignRun {
 protected:
  // How many objects of `type` `ref` reaches.
  static int CountOf(int type, vpiHandle ref) {
    int count = 0;
    vpiHandle it = vpi_iterate(type, ref);
    if (it == nullptr) return 0;
    while (vpi_scan(it) != nullptr) ++count;
    return count;
  }

  // The continuous assignment of the top that is not a net declaration's.
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

// The value of `obj` read as an integer.
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

// §37.47: a module reaches its continuous assignments, the one a net
// declaration makes among them.
TEST_F(ContinuousAssignmentsOfARun, AModuleReachesItsContinuousAssignments) {
  Run(kTwoAssignments);
  EXPECT_EQ(CountOf(vpiContAssign, vpi_handle_by_name(VpiText("top"), nullptr)),
            2);
}

// vpiLhs is the net the assignment drives.
TEST_F(ContinuousAssignmentsOfARun, ItsLeftHandSideIsTheNetItDrives) {
  Run(kTwoAssignments);
  vpiHandle ca = AssignStatementOfTop();
  ASSERT_NE(ca, nullptr);
  EXPECT_STREQ(vpi_get_str(vpiName, vpi_handle(vpiLhs, ca)), "y");
}

// vpiRhs is the expression it assigns, here an operation...
TEST_F(ContinuousAssignmentsOfARun, ItsRightHandSideIsAnOperation) {
  Run(kTwoAssignments);
  vpiHandle ca = AssignStatementOfTop();
  ASSERT_NE(ca, nullptr);
  EXPECT_EQ(vpi_get(vpiType, vpi_handle(vpiRhs, ca)), vpiOperation);
}

// ...whose operator is the one the source wrote...
TEST_F(ContinuousAssignmentsOfARun, TheOperationHasTheSourcesOperator) {
  Run(kTwoAssignments);
  vpiHandle ca = AssignStatementOfTop();
  ASSERT_NE(ca, nullptr);
  EXPECT_EQ(vpi_get(vpiOpType, vpi_handle(vpiRhs, ca)), vpiBitAndOp);
}

// ...and whose operands are the two nets it reads.
TEST_F(ContinuousAssignmentsOfARun, TheOperationsOperandsAreTheNetsItReads) {
  Run(kTwoAssignments);
  vpiHandle ca = AssignStatementOfTop();
  ASSERT_NE(ca, nullptr);
  EXPECT_EQ(NamesOf(vpiOperand, vpi_handle(vpiRhs, ca)),
            (std::vector<std::string>{"a", "b"}));
}

// The assignment a net declaration makes says so.
TEST_F(ContinuousAssignmentsOfARun, ANetDeclarationsAssignmentIsMarked) {
  Run(kTwoAssignments);
  vpiHandle it =
      vpi_iterate(vpiContAssign, vpi_handle_by_name(VpiText("top"), nullptr));
  ASSERT_NE(it, nullptr);
  int marked = 0;
  while (vpiHandle ca = vpi_scan(it)) marked += vpi_get(vpiNetDeclAssign, ca);
  EXPECT_EQ(marked, 1);
}

// §37.46: the assignment is a driver of the net it drives...
TEST_F(ContinuousAssignmentsOfARun, ItDrivesTheNetOnItsLeft) {
  Run(kTwoAssignments);
  EXPECT_EQ(CountOf(vpiDriver, vpi_handle_by_name(VpiText("top.y"), nullptr)),
            1);
}

// ...and a load of every net it reads: a is read by both assignments.
TEST_F(ContinuousAssignmentsOfARun, ItLoadsEachNetItReads) {
  Run(kTwoAssignments);
  EXPECT_EQ(CountOf(vpiLoad, vpi_handle_by_name(VpiText("top.a"), nullptr)), 2);
}

// One assignment to a concatenation is one object, though the elaborator
// splits it into one assignment per element.
TEST_F(ContinuousAssignmentsOfARun, AnAssignmentToAConcatenationIsOneObject) {
  Run("module top; wire [1:0] r; wire p, q; assign {p, q} = r; endmodule\n");
  EXPECT_EQ(CountOf(vpiContAssign, vpi_handle_by_name(VpiText("top"), nullptr)),
            1);
}

// It drives every net of the concatenation.
TEST_F(ContinuousAssignmentsOfARun, AnAssignmentToAConcatenationDrivesEach) {
  Run("module top; wire [1:0] r; wire p, q; assign {p, q} = r; endmodule\n");
  EXPECT_EQ(CountOf(vpiDriver, vpi_handle_by_name(VpiText("top.q"), nullptr)),
            1);
}

// An instance reaches the assignments its own definition wrote.
TEST_F(ContinuousAssignmentsOfARun, AnInstanceReachesItsOwnAssignments) {
  Run("module sub(input c, output d); assign d = ~c; endmodule\n"
      "module top; wire x, z; sub u(.c(x), .d(z)); endmodule\n");
  EXPECT_EQ(
      CountOf(vpiContAssign, vpi_handle_by_name(VpiText("top.u"), nullptr)), 1);
}

// §27.4 with §37.47 and §37.46: a loop generate block makes an instance of
// itself per iteration, each holding its own instance of the continuous
// assignment the block writes, so a two-iteration loop makes two, one in each
// block instance's gen scope (§37.85) and none in the module's, each the
// driver of its own block instance's net. They were one, made for the first
// block instance alone, every instance's assignment coming from the one
// statement a split concatenation's elements do.
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

// §37.47: a continuous assignment's value is that of its right-hand side,
// read as the run now holds it (#7173). Detail 1 and 3: a vector assignment
// has a cont assign bit per bit, each a scalar reaching the assignment as its
// parent, reporting its offset from the least significant bit and holding that
// bit of the assignment's value (#7172). Detail 2: a value change callback
// placed on the assignment is called back as its value changes, and not for a
// write that leaves it as it was, and one placed on a bit as that bit changes
// (#7174).
TEST_F(ContinuousAssignmentsOfARun, AVectorAssignmentHasAValueAndBits) {
  g_assign_changes = 0;
  g_bit_changes = 0;
  s_vpi_systf_data data = {};
  data.type = vpiSysTask;
  data.tfname = VpiText("$watchca");
  data.calltf = &WatchAssignCalltf;
  ASSERT_NE(vpi_register_systf(&data), nullptr);
  data.tfname = VpiText("$unwatchbit");
  data.calltf = &UnwatchBitCalltf;
  ASSERT_NE(vpi_register_systf(&data), nullptr);
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

// §37.47 with §11.6.1 and §10.7: the value a continuous assignment drives is
// its right-hand side evaluated at the width of its left side, so a sum keeps
// the carry an eight-bit target widens it to and loses the bit a three-bit
// target truncates, and the bits above the operands' own width read it
// (#7359).
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
  // The bits of y's assignment at offsets 4 to 7, read as a number.
  int high = 0;
  vpiHandle bit_it = vpi_iterate(vpiBit, y);
  ASSERT_NE(bit_it, nullptr);
  while (vpiHandle bit = vpi_scan(bit_it)) {
    const int kOffset = vpi_get(vpiOffset, bit);
    if (kOffset >= 4) high |= IntValueOf(bit) << (kOffset - 4);
  }
  EXPECT_EQ(high, 1);
}

}  // namespace
}  // namespace delta
