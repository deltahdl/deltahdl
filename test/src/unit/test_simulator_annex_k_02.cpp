// §K.2: vpi_user.h source code — constants and struct definitions

#include <gtest/gtest.h>

#include "simulation/vpi.h"

namespace delta {
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

TEST(VpiAnnexK2, VpiTimeDefaultInit) {
  s_vpi_time time = {};
  EXPECT_EQ(time.type, 0);
  EXPECT_EQ(time.high, 0u);
  EXPECT_EQ(time.low, 0u);
  EXPECT_DOUBLE_EQ(time.real, 0.0);
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

}  // namespace
}  // namespace delta
