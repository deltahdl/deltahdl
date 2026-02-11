// Tests for Annex M (sv_vpi_user.h) — IEEE 1800-2023 SV VPI extensions.
// Verifies all SV-specific VPI constants, types, and assertion API.

#include <gtest/gtest.h>

#include "vpi/sv_vpi_user.h"

namespace {

// =============================================================================
// SV-specific object type constants
// =============================================================================

TEST(SvVpiUser, PackageAndInterfaceTypes) {
  EXPECT_EQ(vpiPackage, 600);
  EXPECT_EQ(vpiInterface, 601);
  EXPECT_EQ(vpiProgram, 602);
  EXPECT_EQ(vpiModport, 606);
  EXPECT_EQ(vpiTypeParameter, 609);
}

TEST(SvVpiUser, VariableTypes) {
  EXPECT_EQ(vpiLongIntVar, 610);
  EXPECT_EQ(vpiIntVar, 612);
  EXPECT_EQ(vpiClassVar, 615);
  EXPECT_EQ(vpiStringVar, 616);
  EXPECT_EQ(vpiEnumVar, 617);
  EXPECT_EQ(vpiStructVar, 618);
  EXPECT_EQ(vpiBitVar, 620);
  EXPECT_EQ(vpiClassObj, 621);
  EXPECT_EQ(vpiChandleVar, 622);
}

TEST(SvVpiUser, TypespecTypes) {
  EXPECT_EQ(vpiLongIntTypespec, 625);
  EXPECT_EQ(vpiEnumTypespec, 632);
  EXPECT_EQ(vpiStructTypespec, 633);
  EXPECT_EQ(vpiInterfaceTypespec, 906);
}

// =============================================================================
// Assertion types
// =============================================================================

TEST(SvVpiUser, AssertionTypes) {
  EXPECT_EQ(vpiAssert, 686);
  EXPECT_EQ(vpiAssume, 687);
  EXPECT_EQ(vpiCover, 688);
  EXPECT_EQ(vpiRestrict, 901);
  EXPECT_EQ(vpiImmediateAssert, 665);
}

// =============================================================================
// Operator constants
// =============================================================================

TEST(SvVpiUser, OperatorConstants) {
  EXPECT_EQ(vpiImplyOp, 50);
  EXPECT_EQ(vpiPostIncOp, 62);
  EXPECT_EQ(vpiWildEqOp, 69);
  EXPECT_EQ(vpiStreamLROp, 71);
  EXPECT_EQ(vpiInsideOp, 95);
  EXPECT_EQ(vpiNexttimeOp, 89);
  EXPECT_EQ(vpiAlwaysOp, 90);
  EXPECT_EQ(vpiEventuallyOp, 91);
}

// =============================================================================
// Object properties
// =============================================================================

TEST(SvVpiUser, JoinTypeConstants) {
  EXPECT_EQ(vpiJoin, 0);
  EXPECT_EQ(vpiJoinNone, 1);
  EXPECT_EQ(vpiJoinAny, 2);
}

TEST(SvVpiUser, RandTypeConstants) {
  EXPECT_EQ(vpiNotRand, 1);
  EXPECT_EQ(vpiRand, 2);
  EXPECT_EQ(vpiRandC, 3);
}

TEST(SvVpiUser, VisibilityConstants) {
  EXPECT_EQ(vpiPublicVis, 1);
  EXPECT_EQ(vpiProtectedVis, 2);
  EXPECT_EQ(vpiLocalVis, 3);
}

TEST(SvVpiUser, AlwaysTypeConstants) {
  EXPECT_EQ(vpiAlwaysComb, 2);
  EXPECT_EQ(vpiAlwaysFF, 3);
  EXPECT_EQ(vpiAlwaysLatch, 4);
}

// =============================================================================
// Callback reason constants
// =============================================================================

TEST(SvVpiUser, AssertionCallbackReasons) {
  EXPECT_EQ(cbAssertionStart, 606);
  EXPECT_EQ(cbAssertionSuccess, 607);
  EXPECT_EQ(cbAssertionFailure, 608);
  EXPECT_EQ(cbAssertionDisable, 611);
  EXPECT_EQ(cbAssertionKill, 614);
}

TEST(SvVpiUser, ThreadCallbackReasons) {
  EXPECT_EQ(cbStartOfThread, 600);
  EXPECT_EQ(cbEndOfThread, 601);
  EXPECT_EQ(cbCreateObj, 700);
}

// =============================================================================
// Coverage VPI constants
// =============================================================================

TEST(SvVpiUser, CoverageControlConstants) {
  EXPECT_EQ(vpiCoverageStart, 750);
  EXPECT_EQ(vpiCoverageStop, 751);
  EXPECT_EQ(vpiCoverageReset, 752);
  EXPECT_EQ(vpiCoverageCheck, 753);
}

TEST(SvVpiUser, CoverageTypeConstants) {
  EXPECT_EQ(vpiAssertCoverage, 760);
  EXPECT_EQ(vpiStatementCoverage, 762);
  EXPECT_EQ(vpiToggleCoverage, 763);
  EXPECT_EQ(vpiCovered, 765);
}

// =============================================================================
// Assertion control constants
// =============================================================================

TEST(SvVpiUser, AssertionControlConstants) {
  EXPECT_EQ(vpiAssertionDisable, 620);
  EXPECT_EQ(vpiAssertionEnable, 621);
  EXPECT_EQ(vpiAssertionReset, 622);
  EXPECT_EQ(vpiAssertionKill, 623);
}

// =============================================================================
// Assertion API structures
// =============================================================================

TEST(SvVpiUser, AssertionStepInfoStruct) {
  s_vpi_assertion_step_info info = {};
  info.matched_expression_count = 3;
  info.state_from = 1;
  info.state_to = 2;
  EXPECT_EQ(info.matched_expression_count, 3);
  EXPECT_EQ(info.state_from, 1);
  EXPECT_EQ(info.state_to, 2);
}

TEST(SvVpiUser, AttemptInfoStruct) {
  s_vpi_attempt_info info = {};
  info.attempt_start_time.type = vpiSimTime;
  info.attempt_start_time.low = 100;
  info.detail.fail_expr = nullptr;
  EXPECT_EQ(info.attempt_start_time.type, vpiSimTime);
  EXPECT_EQ(info.attempt_start_time.low, 100u);
}

// =============================================================================
// Assertion callback registration function
// =============================================================================

TEST(SvVpiUser, RegisterAssertionCbReturnsNull) {
  vpiHandle result =
      vpi_register_assertion_cb(nullptr, cbAssertionStart, nullptr, nullptr);
  EXPECT_EQ(result, nullptr);
}

// =============================================================================
// DPI access type constants
// =============================================================================

TEST(SvVpiUser, DpiAccessTypeConstants) {
  EXPECT_EQ(vpiForkJoinAcc, 1);
  EXPECT_EQ(vpiDPIExportAcc, 3);
  EXPECT_EQ(vpiDPIImportAcc, 4);
}

}  // namespace
