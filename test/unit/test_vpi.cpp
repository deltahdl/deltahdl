#include <gtest/gtest.h>

#include "simulation/vpi.h"

namespace delta {
namespace {

class VpiTest : public ::testing::Test {
 protected:
  void SetUp() override { SetGlobalVpiContext(&ctx_); }
  void TearDown() override { SetGlobalVpiContext(nullptr); }

  VpiContext ctx_;
};

// --- Value format constants ---

TEST_F(VpiTest, ValueFormatConstants) {
  EXPECT_EQ(vpiBinStrVal, 1);
  EXPECT_EQ(vpiOctStrVal, 2);
  EXPECT_EQ(vpiHexStrVal, 3);
  EXPECT_EQ(vpiScalarVal, 4);
  EXPECT_EQ(vpiIntVal, 5);
  EXPECT_EQ(vpiRealVal, 6);
  EXPECT_EQ(vpiStringVal, 7);
}

// --- Object type constants ---

TEST_F(VpiTest, ObjectTypeConstants) {
  EXPECT_EQ(vpiModule, 32);
  EXPECT_EQ(vpiNet, 36);
  EXPECT_EQ(vpiReg, 48);
  EXPECT_EQ(vpiPort, 44);
  EXPECT_EQ(vpiCallback, 107);
}

// --- Time type constants ---

TEST_F(VpiTest, TimeTypeConstants) {
  EXPECT_EQ(vpiSimTime, 1);
  EXPECT_EQ(vpiScaledRealTime, 2);
}

// --- Callback reason constants ---

TEST_F(VpiTest, CallbackReasonConstants) {
  EXPECT_EQ(cbValueChange, 1);
  EXPECT_EQ(cbReadWriteSynch, 2);
  EXPECT_EQ(cbEndOfSimulation, 3);
}

// --- System task registration ---

TEST_F(VpiTest, RegisterSystfStoresTask) {
  s_vpi_systf_data data = {};
  data.type = vpiSysTask;
  data.tfname = "$hello";
  vpi_register_systf(&data);

  ASSERT_EQ(ctx_.RegisteredSystfs().size(), 1);
  EXPECT_EQ(ctx_.RegisteredSystfs()[0].type, vpiSysTask);
  EXPECT_STREQ(ctx_.RegisteredSystfs()[0].tfname, "$hello");
}

TEST_F(VpiTest, RegisterMultipleSystfs) {
  s_vpi_systf_data data1 = {};
  data1.type = vpiSysTask;
  data1.tfname = "$task_a";

  s_vpi_systf_data data2 = {};
  data2.type = vpiSysFunc;
  data2.tfname = "$func_b";

  vpi_register_systf(&data1);
  vpi_register_systf(&data2);

  ASSERT_EQ(ctx_.RegisteredSystfs().size(), 2);
  EXPECT_STREQ(ctx_.RegisteredSystfs()[0].tfname, "$task_a");
  EXPECT_STREQ(ctx_.RegisteredSystfs()[1].tfname, "$func_b");
  EXPECT_EQ(ctx_.RegisteredSystfs()[1].type, vpiSysFunc);
}

TEST_F(VpiTest, RegisterSystfNullptrDoesNotCrash) {
  vpiHandle h = vpi_register_systf(nullptr);
  EXPECT_EQ(h, nullptr);
  EXPECT_TRUE(ctx_.RegisteredSystfs().empty());
}

// --- Handle by name ---

TEST_F(VpiTest, HandleByNameReturnsNullptrForUnknown) {
  vpiHandle h = vpi_handle_by_name("top.clk", nullptr);
  EXPECT_EQ(h, nullptr);
}

TEST_F(VpiTest, HandleByNameWithScopeReturnsNullptr) {
  vpiHandle h = vpi_handle_by_name("submod.sig", nullptr);
  EXPECT_EQ(h, nullptr);
}

// --- Iterate / Scan ---

TEST_F(VpiTest, IterateReturnsNullptr) {
  vpiHandle iter = vpi_iterate(vpiModule, nullptr);
  EXPECT_EQ(iter, nullptr);
}

TEST_F(VpiTest, ScanReturnsNullptr) {
  vpiHandle obj = vpi_scan(nullptr);
  EXPECT_EQ(obj, nullptr);
}

// --- Get value / Put value ---

TEST_F(VpiTest, GetValueNullptrHandleDoesNotCrash) {
  s_vpi_value val = {};
  val.format = vpiIntVal;
  vpi_get_value(nullptr, &val);
  // Should not crash; value remains unchanged.
  EXPECT_EQ(val.format, vpiIntVal);
}

TEST_F(VpiTest, GetValueNullptrValueDoesNotCrash) {
  vpi_get_value(nullptr, nullptr);
  // Should not crash.
}

TEST_F(VpiTest, PutValueNullptrHandleDoesNotCrash) {
  s_vpi_value val = {};
  val.format = vpiIntVal;
  val.value.integer = 42;
  s_vpi_time time = {};
  time.type = vpiSimTime;
  vpi_put_value(nullptr, &val, &time, 0);
  // Should not crash.
}

// --- Get / GetStr ---

TEST_F(VpiTest, GetReturnsZeroForStub) {
  int result = vpi_get(vpiModule, nullptr);
  EXPECT_EQ(result, 0);
}

TEST_F(VpiTest, GetStrReturnsNullptrForStub) {
  const char* result = vpi_get_str(vpiModule, nullptr);
  EXPECT_EQ(result, nullptr);
}

// --- Free object ---

TEST_F(VpiTest, FreeObjectNullptrDoesNotCrash) {
  int result = vpi_free_object(nullptr);
  EXPECT_EQ(result, 0);
}

// --- Callback registration ---

TEST_F(VpiTest, RegisterCbStoresCallback) {
  s_cb_data cb = {};
  cb.reason = cbValueChange;
  cb.obj = nullptr;
  vpi_register_cb(&cb);

  ASSERT_EQ(ctx_.RegisteredCallbacks().size(), 1);
  EXPECT_EQ(ctx_.RegisteredCallbacks()[0].reason, cbValueChange);
}

TEST_F(VpiTest, RegisterMultipleCallbacks) {
  s_cb_data cb1 = {};
  cb1.reason = cbValueChange;

  s_cb_data cb2 = {};
  cb2.reason = cbEndOfSimulation;

  vpi_register_cb(&cb1);
  vpi_register_cb(&cb2);

  ASSERT_EQ(ctx_.RegisteredCallbacks().size(), 2);
  EXPECT_EQ(ctx_.RegisteredCallbacks()[0].reason, cbValueChange);
  EXPECT_EQ(ctx_.RegisteredCallbacks()[1].reason, cbEndOfSimulation);
}

TEST_F(VpiTest, RegisterCbNullptrDoesNotCrash) {
  vpiHandle h = vpi_register_cb(nullptr);
  EXPECT_EQ(h, nullptr);
  EXPECT_TRUE(ctx_.RegisteredCallbacks().empty());
}

// --- Struct default initialization ---

TEST_F(VpiTest, VpiValueDefaultInit) {
  s_vpi_value val = {};
  EXPECT_EQ(val.format, 0);
}

TEST_F(VpiTest, VpiTimeDefaultInit) {
  s_vpi_time time = {};
  EXPECT_EQ(time.type, 0);
  EXPECT_EQ(time.high, 0u);
  EXPECT_EQ(time.low, 0u);
  EXPECT_DOUBLE_EQ(time.real, 0.0);
}

TEST_F(VpiTest, VpiCbDataDefaultInit) {
  s_cb_data cb = {};
  EXPECT_EQ(cb.reason, 0);
  EXPECT_EQ(cb.obj, nullptr);
  EXPECT_EQ(cb.time, nullptr);
  EXPECT_EQ(cb.value, nullptr);
  EXPECT_EQ(cb.user_data, nullptr);
}

TEST_F(VpiTest, VpiSystfDataDefaultInit) {
  s_vpi_systf_data data = {};
  EXPECT_EQ(data.type, 0);
  EXPECT_EQ(data.tfname, nullptr);
  EXPECT_EQ(data.calltf, nullptr);
  EXPECT_EQ(data.user_data, nullptr);
}

// --- Global context management ---

TEST(VpiContextTest, DefaultContextIsAvailable) {
  SetGlobalVpiContext(nullptr);
  VpiContext& ctx = GetGlobalVpiContext();
  // Should return the default context without crashing.
  (void)ctx;
}

TEST(VpiContextTest, SetAndGetContext) {
  VpiContext custom;
  SetGlobalVpiContext(&custom);

  s_vpi_systf_data data = {};
  data.tfname = "$custom";
  vpi_register_systf(&data);

  EXPECT_EQ(custom.RegisteredSystfs().size(), 1);
  EXPECT_STREQ(custom.RegisteredSystfs()[0].tfname, "$custom");

  SetGlobalVpiContext(nullptr);
}

}  // namespace
}  // namespace delta
