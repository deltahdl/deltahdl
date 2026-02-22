// Annex M.2: Source code

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
  struct {
    int actual;
    int expected;
  } const kCases[] = {
      {vpiLongIntVar, 610}, {vpiIntVar, 612},   {vpiClassVar, 615},
      {vpiStringVar, 616},  {vpiEnumVar, 617},  {vpiStructVar, 618},
      {vpiBitVar, 620},     {vpiClassObj, 621}, {vpiChandleVar, 622},
  };
  for (const auto &c : kCases) {
    EXPECT_EQ(c.actual, c.expected);
  }
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
  struct {
    int actual;
    int expected;
  } const kCases[] = {
      {vpiImplyOp, 50},    {vpiPostIncOp, 62},    {vpiWildEqOp, 69},
      {vpiStreamLROp, 71}, {vpiInsideOp, 95},     {vpiNexttimeOp, 89},
      {vpiAlwaysOp, 90},   {vpiEventuallyOp, 91},
  };
  for (const auto &c : kCases) {
    EXPECT_EQ(c.actual, c.expected);
  }
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

TEST(SvVpiUser, ThreadCallbackReasons) {
  EXPECT_EQ(cbStartOfThread, 600);
  EXPECT_EQ(cbEndOfThread, 601);
  EXPECT_EQ(cbCreateObj, 700);
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
