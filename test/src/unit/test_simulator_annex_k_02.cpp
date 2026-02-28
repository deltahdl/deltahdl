// Annex K.2: Source code

#include <gtest/gtest.h>

#include "simulator/vpi.h"

namespace {

TEST(VpiAnnexK2, ValueFormatConstants) {
  EXPECT_EQ(vpiBinStrVal, 1);
  EXPECT_EQ(vpiOctStrVal, 2);
  EXPECT_EQ(vpiHexStrVal, 3);
  EXPECT_EQ(vpiScalarVal, 4);
  EXPECT_EQ(vpiIntVal, 5);
  EXPECT_EQ(vpiRealVal, 6);
  EXPECT_EQ(vpiStringVal, 7);
}

TEST(VpiAnnexK2, ObjectTypeConstants) {
  EXPECT_EQ(vpiModule, 32);
  EXPECT_EQ(vpiNet, 36);
  EXPECT_EQ(vpiReg, 48);
  EXPECT_EQ(vpiPort, 44);
  EXPECT_EQ(vpiCallback, 107);
}

TEST(VpiAnnexK2, TimeTypeConstants) {
  EXPECT_EQ(vpiSimTime, 1);
  EXPECT_EQ(vpiScaledRealTime, 2);
}

TEST(VpiAnnexK2, CallbackReasonConstants) {
  EXPECT_EQ(cbValueChange, 1);
  EXPECT_EQ(cbReadWriteSynch, 2);
  EXPECT_EQ(cbEndOfSimulation, 3);
}

TEST(VpiAnnexK2, VpiValueDefaultInit) {
  s_vpi_value val = {};
  EXPECT_EQ(val.format, 0);
}

TEST(VpiAnnexK2, VpiCbDataDefaultInit) {
  s_cb_data cb = {};
  EXPECT_EQ(cb.reason, 0);
  EXPECT_EQ(cb.obj, nullptr);
  EXPECT_EQ(cb.time, nullptr);
  EXPECT_EQ(cb.value, nullptr);
  EXPECT_EQ(cb.user_data, nullptr);
}

TEST(VpiAnnexK2, VpiSystfDataDefaultInit) {
  s_vpi_systf_data data = {};
  EXPECT_EQ(data.type, 0);
  EXPECT_EQ(data.tfname, nullptr);
  EXPECT_EQ(data.calltf, nullptr);
  EXPECT_EQ(data.user_data, nullptr);
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

}  // namespace
