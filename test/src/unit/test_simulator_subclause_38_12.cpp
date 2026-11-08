#include <gtest/gtest.h>

#include "simulator/vpi_context.h"
#include "simulator/vpi_globals.h"
#include "simulator/vpi_internal.h"
#include "simulator/vpi_object.h"
#include "simulator/vpi_user.h"

namespace delta {
namespace {

PLI_INT32 InfoStubCall(PLI_BYTE8*) { return 0; }
PLI_INT32 InfoStubCompile(PLI_BYTE8*) { return 0; }
PLI_INT32 InfoStubSize(PLI_BYTE8*) { return 0; }

class VpiGetSystfInfoSim : public ::testing::Test {
 protected:
  void SetUp() override { SetGlobalVpiContext(&vpi_ctx_); }
  void TearDown() override { SetGlobalVpiContext(nullptr); }

  VpiContext vpi_ctx_;
};

TEST_F(VpiGetSystfInfoSim, FillsStructFromSystfCallbackHandle) {
  int payload = 42;
  s_vpi_systf_data registered = {};
  registered.type = vpiSysFunc;
  registered.sysfunctype = vpiSysFunc;
  registered.tfname = VpiText("$probe");
  registered.calltf = &InfoStubCall;
  registered.compiletf = &InfoStubCompile;
  registered.sizetf = &InfoStubSize;
  registered.user_data = reinterpret_cast<PLI_BYTE8*>(&payload);

  vpiHandle h = vpi_register_systf(&registered);
  ASSERT_NE(h, nullptr);

  s_vpi_systf_data out = {};
  vpi_get_systf_info(h, &out);

  EXPECT_EQ(out.type, vpiSysFunc);
  EXPECT_EQ(out.sysfunctype, vpiSysFunc);
  EXPECT_STREQ(out.tfname, "$probe");
  EXPECT_EQ(out.calltf, &InfoStubCall);
  EXPECT_EQ(out.compiletf, &InfoStubCompile);
  EXPECT_EQ(out.sizetf, &InfoStubSize);
  EXPECT_EQ(out.user_data, reinterpret_cast<PLI_BYTE8*>(&payload));
}

TEST_F(VpiGetSystfInfoSim, ReportsTheCallbackNamedByTheHandle) {
  s_vpi_systf_data first = {};
  first.type = vpiSysTask;
  first.tfname = VpiText("$first");

  s_vpi_systf_data second = {};
  second.type = vpiSysFunc;
  second.sysfunctype = vpiIntFunc;
  second.tfname = VpiText("$second");

  vpiHandle h1 = vpi_register_systf(&first);
  vpiHandle h2 = vpi_register_systf(&second);

  s_vpi_systf_data out1 = {};
  s_vpi_systf_data out2 = {};
  vpi_get_systf_info(h1, &out1);
  vpi_get_systf_info(h2, &out2);

  EXPECT_STREQ(out1.tfname, "$first");
  EXPECT_EQ(out1.type, vpiSysTask);
  EXPECT_STREQ(out2.tfname, "$second");
  EXPECT_EQ(out2.type, vpiSysFunc);
}

TEST_F(VpiGetSystfInfoSim, WritesIntoApplicationAllocatedMemory) {
  s_vpi_systf_data registered = {};
  registered.type = vpiSysTask;
  registered.tfname = VpiText("$measure");

  vpiHandle h = vpi_register_systf(&registered);
  ASSERT_NE(h, nullptr);

  s_vpi_systf_data caller_owned = {};
  s_vpi_systf_data* before = &caller_owned;
  vpi_get_systf_info(h, &caller_owned);

  EXPECT_EQ(before, &caller_owned);
  EXPECT_STREQ(caller_owned.tfname, "$measure");
  EXPECT_EQ(caller_owned.type, vpiSysTask);
}

TEST_F(VpiGetSystfInfoSim, NullArgumentsAreSafe) {
  s_vpi_systf_data registered = {};
  registered.type = vpiSysTask;
  registered.tfname = VpiText("$safe");
  vpiHandle h = vpi_register_systf(&registered);
  ASSERT_NE(h, nullptr);

  s_vpi_systf_data out = {};
  out.tfname = VpiText("untouched");

  vpi_get_systf_info(nullptr, &out);
  vpi_get_systf_info(h, nullptr);
  vpi_get_systf_info(nullptr, nullptr);

  EXPECT_STREQ(out.tfname, "untouched");
}

TEST_F(VpiGetSystfInfoSim, NonSystfCallbackLeavesDestinationUnchanged) {
  s_cb_data cb = {};
  vpiHandle cb_handle = vpi_register_cb(&cb);
  ASSERT_NE(cb_handle, nullptr);

  s_vpi_systf_data out = {};
  out.tfname = VpiText("untouched");
  vpi_get_systf_info(cb_handle, &out);

  EXPECT_STREQ(out.tfname, "untouched");
}

TEST_F(VpiGetSystfInfoSim, NonCallbackHandleLeavesDestinationUnchanged) {
  VpiHandle module = vpi_ctx_.CreateModule("top", "top");
  ASSERT_NE(module, nullptr);

  s_vpi_systf_data out = {};
  out.tfname = VpiText("untouched");
  vpi_get_systf_info(VpiHandleOf(module), &out);

  EXPECT_STREQ(out.tfname, "untouched");
}

TEST_F(VpiGetSystfInfoSim, ASystemTaskCallIsNotTheCallbackTheRoutineReports) {
  s_vpi_systf_data registered = {};
  registered.type = vpiSysTask;
  registered.tfname = VpiText("$measure");
  ASSERT_NE(vpi_register_systf(&registered), nullptr);

  VpiObject call;
  call.type = vpiSysTaskCall;
  call.name = "$measure";

  s_vpi_systf_data out = {};
  out.tfname = VpiText("untouched");
  vpi_get_systf_info(VpiHandleOf(&call), &out);

  EXPECT_STREQ(out.tfname, "untouched");
}

TEST_F(VpiGetSystfInfoSim, TheRegistrationIsReportedAsOftenAsItIsAsked) {
  int payload = 9;
  s_vpi_systf_data registered = {};
  registered.type = vpiSysFunc;
  registered.sysfunctype = vpiIntFunc;
  registered.tfname = VpiText("$probe");
  registered.calltf = &InfoStubCall;
  registered.user_data = reinterpret_cast<PLI_BYTE8*>(&payload);

  vpiHandle h = vpi_register_systf(&registered);
  ASSERT_NE(h, nullptr);

  s_vpi_systf_data out = {};
  vpi_get_systf_info(h, &out);
  ASSERT_STREQ(out.tfname, "$probe");

  out.tfname = VpiText("overwritten");
  out.calltf = nullptr;
  out.user_data = nullptr;
  vpi_get_systf_info(h, &out);

  EXPECT_STREQ(out.tfname, "$probe");
  EXPECT_EQ(out.sysfunctype, vpiIntFunc);
  EXPECT_EQ(out.calltf, &InfoStubCall);
  EXPECT_EQ(out.user_data, reinterpret_cast<PLI_BYTE8*>(&payload));
}

}  // namespace
}  // namespace delta
