#include <gtest/gtest.h>

#include "simulator/vpi.h"

namespace delta {
namespace {

class VpiSystfRegistrationSim : public ::testing::Test {
 protected:
  void SetUp() override { SetGlobalVpiContext(&vpi_ctx_); }
  void TearDown() override { SetGlobalVpiContext(nullptr); }

  VpiContext vpi_ctx_;
};

TEST_F(VpiSystfRegistrationSim, RegisterMultipleSystfs) {
  s_vpi_systf_data data1 = {};
  data1.type = vpiSysTask;
  data1.tfname = "$task_a";

  s_vpi_systf_data data2 = {};
  data2.type = vpiSysFunc;
  data2.tfname = "$func_b";

  vpi_register_systf(&data1);
  vpi_register_systf(&data2);

  ASSERT_EQ(vpi_ctx_.RegisteredSystfs().size(), 2);
  EXPECT_STREQ(vpi_ctx_.RegisteredSystfs()[0].tfname, "$task_a");
  EXPECT_STREQ(vpi_ctx_.RegisteredSystfs()[1].tfname, "$func_b");
  EXPECT_EQ(vpi_ctx_.RegisteredSystfs()[1].type, vpiSysFunc);
}

TEST_F(VpiSystfRegistrationSim, RegisterSystfReturnsDistinctHandles) {
  s_vpi_systf_data task = {};
  task.type = vpiSysTask;
  task.tfname = "$first";

  s_vpi_systf_data func = {};
  func.type = vpiSysFunc;
  func.tfname = "$second";

  vpiHandle h1 = vpi_register_systf(&task);
  vpiHandle h2 = vpi_register_systf(&func);

  // §38.37 Returns row: every registration produces its own callback object,
  // so distinct registrations must hand back distinct, non-null handles.
  ASSERT_NE(h1, nullptr);
  ASSERT_NE(h2, nullptr);
  EXPECT_NE(h1, h2);
  EXPECT_EQ(vpi_get(vpiType, h1), vpiCallback);
  EXPECT_EQ(vpi_get(vpiType, h2), vpiCallback);
}

namespace {
int SystfStubCall(const char*) { return 0; }
int SystfStubCompile(const char*) { return 0; }
int SystfStubSize(const char*) { return 0; }
}  // namespace

TEST_F(VpiSystfRegistrationSim, RegisterSystfPreservesFigure3818Fields) {
  int user_payload = 7;
  s_vpi_systf_data data = {};
  data.type = vpiSysFunc;
  data.sysfunctype = vpiSysFunc;
  data.tfname = "$measure";
  data.calltf = &SystfStubCall;
  data.compiletf = &SystfStubCompile;
  data.sizetf = &SystfStubSize;
  data.user_data = &user_payload;

  vpi_register_systf(&data);

  // §38.37: systf_data_p points to a s_vpi_systf_data structure as listed in
  // Figure 38-18. Confirm registration preserves the whole structure shape,
  // i.e. every Figure 38-18 member survives the call.
  ASSERT_EQ(vpi_ctx_.RegisteredSystfs().size(), 1);
  const auto& stored = vpi_ctx_.RegisteredSystfs()[0];
  EXPECT_EQ(stored.type, vpiSysFunc);
  EXPECT_EQ(stored.sysfunctype, vpiSysFunc);
  EXPECT_STREQ(stored.tfname, "$measure");
  EXPECT_EQ(stored.calltf, &SystfStubCall);
  EXPECT_EQ(stored.compiletf, &SystfStubCompile);
  EXPECT_EQ(stored.sizetf, &SystfStubSize);
  EXPECT_EQ(stored.user_data, &user_payload);
}

TEST_F(VpiSystfRegistrationSim, RegisterSystfNullptrDoesNotCrash) {
  vpiHandle h = vpi_register_systf(nullptr);
  EXPECT_EQ(h, nullptr);
  EXPECT_TRUE(vpi_ctx_.RegisteredSystfs().empty());
}

}  // namespace
}  // namespace delta
