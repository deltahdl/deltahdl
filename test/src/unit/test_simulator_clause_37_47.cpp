#include <gtest/gtest.h>

#include "simulator/sv_vpi_user.h"
#include "simulator/vpi.h"

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
  EXPECT_EQ(vpi_get(vpiSize, &bit), 1);

  VpiObject assign;
  assign.type = vpiContAssign;
  assign.size = 4;
  EXPECT_EQ(vpi_get(vpiSize, &assign), 4);
}

// Detail 3: vpiOffset shall return zero for the LSB. The offset is measured
// from the least significant bit, so the LSB bit reports zero and a bit three
// positions above it reports three.
TEST_F(ContinuousAssignment, LsbContAssignBitReportsZeroOffset) {
  VpiObject lsb;
  lsb.type = vpiContAssignBit;
  lsb.offset = 0;
  EXPECT_EQ(vpi_get(vpiOffset, &lsb), 0);

  VpiObject higher;
  higher.type = vpiContAssignBit;
  higher.offset = 3;
  EXPECT_EQ(vpi_get(vpiOffset, &higher), 3);
}

// Diagram property: a continuous assignment reports through vpiNetDeclAssign
// whether it is a net declaration assignment. An assignment marked as such
// reports TRUE; an ordinary assign statement reports FALSE.
TEST_F(ContinuousAssignment, ReportsNetDeclAssign) {
  VpiObject net_decl;
  net_decl.type = vpiContAssign;
  net_decl.net_decl_assign = true;
  EXPECT_EQ(vpi_get(vpiNetDeclAssign, &net_decl), 1);

  VpiObject standalone;
  standalone.type = vpiContAssign;
  EXPECT_EQ(vpi_get(vpiNetDeclAssign, &standalone), 0);
}

// Diagram property: a continuous assignment reports the drive strengths it
// carries on its 0 and 1 values through vpiStrength0 and vpiStrength1.
TEST_F(ContinuousAssignment, ReportsDriveStrengths) {
  VpiObject assign;
  assign.type = vpiContAssign;
  assign.strength0 = vpiPullDrive;
  assign.strength1 = vpiStrongDrive;
  EXPECT_EQ(vpi_get(vpiStrength0, &assign), vpiPullDrive);
  EXPECT_EQ(vpi_get(vpiStrength1, &assign), vpiStrongDrive);
}

// Detail 2: a value change callback may be placed onto a cont assign or onto a
// cont assign bit. Neither object kind is rejected by registration, so both
// hand back a live callback handle.
TEST_F(ContinuousAssignment, ValueChangeCallbackAllowedOnContAssignAndBit) {
  VpiObject assign;
  assign.type = vpiContAssign;
  VpiCbData on_assign = {};
  on_assign.reason = cbValueChange;
  on_assign.obj = &assign;
  EXPECT_NE(ctx_.RegisterCb(&on_assign), nullptr);

  VpiObject bit;
  bit.type = vpiContAssignBit;
  VpiCbData on_bit = {};
  on_bit.reason = cbValueChange;
  on_bit.obj = &bit;
  EXPECT_NE(ctx_.RegisterCb(&on_bit), nullptr);
}

}  // namespace
}  // namespace delta
