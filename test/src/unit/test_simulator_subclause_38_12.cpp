#include <gtest/gtest.h>

#include "simulator/vpi.h"

namespace delta {
namespace {

int InfoStubCall(const char*) { return 0; }
int InfoStubCompile(const char*) { return 0; }
int InfoStubSize(const char*) { return 0; }

class VpiGetSystfInfoSim : public ::testing::Test {
 protected:
  void SetUp() override { SetGlobalVpiContext(&vpi_ctx_); }
  void TearDown() override { SetGlobalVpiContext(nullptr); }

  VpiContext vpi_ctx_;
};

// §38.12 shall #1 + Figure 38-5: given a handle to a system task/function
// callback, the routine reports its registration in an s_vpi_systf_data
// structure. Every Figure 38-5 member must survive the round trip.
TEST_F(VpiGetSystfInfoSim, FillsStructFromSystfCallbackHandle) {
  int payload = 42;
  s_vpi_systf_data registered = {};
  registered.type = vpiSysFunc;
  registered.sysfunctype = vpiSysFunc;
  registered.tfname = "$probe";
  registered.calltf = &InfoStubCall;
  registered.compiletf = &InfoStubCompile;
  registered.sizetf = &InfoStubSize;
  registered.user_data = &payload;

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
  EXPECT_EQ(out.user_data, &payload);
}

// §38.12 shall #1: each registered callback is reported on its own; asking
// about the second handle yields the second registration, not the first.
TEST_F(VpiGetSystfInfoSim, ReportsTheCallbackNamedByTheHandle) {
  s_vpi_systf_data first = {};
  first.type = vpiSysTask;
  first.tfname = "$first";

  s_vpi_systf_data second = {};
  second.type = vpiSysFunc;
  second.tfname = "$second";

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

// §38.12 shall #2: the destination memory belongs to the application. The
// routine fills a caller-owned structure in place rather than allocating one,
// so a local on the caller's stack is populated and its address is unchanged.
TEST_F(VpiGetSystfInfoSim, WritesIntoApplicationAllocatedMemory) {
  s_vpi_systf_data registered = {};
  registered.type = vpiSysTask;
  registered.tfname = "$measure";

  vpiHandle h = vpi_register_systf(&registered);
  ASSERT_NE(h, nullptr);

  s_vpi_systf_data caller_owned = {};
  s_vpi_systf_data* before = &caller_owned;
  vpi_get_systf_info(h, &caller_owned);

  // The application's own object is the one that received the data.
  EXPECT_EQ(before, &caller_owned);
  EXPECT_STREQ(caller_owned.tfname, "$measure");
  EXPECT_EQ(caller_owned.type, vpiSysTask);
}

// §38.12 Arguments (mandatory per §38.1): both the handle and the destination
// pointer are required. Missing either leaves nothing to do and must be safe.
TEST_F(VpiGetSystfInfoSim, NullArgumentsAreSafe) {
  s_vpi_systf_data registered = {};
  registered.type = vpiSysTask;
  registered.tfname = "$safe";
  vpiHandle h = vpi_register_systf(&registered);
  ASSERT_NE(h, nullptr);

  s_vpi_systf_data out = {};
  out.tfname = "untouched";

  vpi_get_systf_info(nullptr, &out);  // no handle
  vpi_get_systf_info(h, nullptr);     // no destination
  vpi_get_systf_info(nullptr, nullptr);

  // The destination supplied with the null-handle call was left as the caller
  // initialized it.
  EXPECT_STREQ(out.tfname, "untouched");
}

// §38.12 Arguments: obj is a handle to a system task/function callback.
// A callback object that is not a registered system task/function (e.g. a
// simulation callback) names no s_vpi_systf_data, so the destination is left
// as the caller initialized it.
TEST_F(VpiGetSystfInfoSim, NonSystfCallbackLeavesDestinationUnchanged) {
  s_cb_data cb = {};
  vpiHandle cb_handle = vpi_register_cb(&cb);
  ASSERT_NE(cb_handle, nullptr);

  s_vpi_systf_data out = {};
  out.tfname = "untouched";
  vpi_get_systf_info(cb_handle, &out);

  EXPECT_STREQ(out.tfname, "untouched");
}

// §38.12 Arguments: obj is a handle to a system task/function callback. A
// handle to an object that is not a callback at all (here a module instance)
// names no s_vpi_systf_data, so the destination is left untouched.
TEST_F(VpiGetSystfInfoSim, NonCallbackHandleLeavesDestinationUnchanged) {
  vpiHandle module = vpi_ctx_.CreateModule("top", "top");
  ASSERT_NE(module, nullptr);

  s_vpi_systf_data out = {};
  out.tfname = "untouched";
  vpi_get_systf_info(module, &out);

  EXPECT_STREQ(out.tfname, "untouched");
}

// §38.12 Arguments: obj is a handle to the system task or function *callback* -
// the object vpi_register_systf() handed back. The object an application holds
// while its calltf runs is a different one: §37.42 detail 3 reaches the system
// task call itself through vpi_handle(vpiSysTfCall, NULL), and a call is not
// the registration, so the routine reports nothing for it. This is the nearest
// thing to a systf callback that is not one.
TEST_F(VpiGetSystfInfoSim, ASystemTaskCallIsNotTheCallbackTheRoutineReports) {
  s_vpi_systf_data registered = {};
  registered.type = vpiSysTask;
  registered.tfname = "$measure";
  ASSERT_NE(vpi_register_systf(&registered), nullptr);

  VpiObject call;
  call.type = vpiSysTaskCall;
  call.name = "$measure";

  s_vpi_systf_data out = {};
  out.tfname = "untouched";
  vpi_get_systf_info(&call, &out);

  EXPECT_STREQ(out.tfname, "untouched");
}

// §38.12 reports the registration, which reading does not consume: the same
// handle answers the same way however often it is asked, and a structure the
// caller has since written over is filled again rather than left as it was.
TEST_F(VpiGetSystfInfoSim, TheRegistrationIsReportedAsOftenAsItIsAsked) {
  int payload = 9;
  s_vpi_systf_data registered = {};
  registered.type = vpiSysFunc;
  registered.sysfunctype = vpiIntFunc;
  registered.tfname = "$probe";
  registered.calltf = &InfoStubCall;
  registered.user_data = &payload;

  vpiHandle h = vpi_register_systf(&registered);
  ASSERT_NE(h, nullptr);

  s_vpi_systf_data out = {};
  vpi_get_systf_info(h, &out);
  ASSERT_STREQ(out.tfname, "$probe");

  out.tfname = "overwritten";
  out.calltf = nullptr;
  out.user_data = nullptr;
  vpi_get_systf_info(h, &out);

  EXPECT_STREQ(out.tfname, "$probe");
  EXPECT_EQ(out.sysfunctype, vpiIntFunc);
  EXPECT_EQ(out.calltf, &InfoStubCall);
  EXPECT_EQ(out.user_data, &payload);
}

}  // namespace
}  // namespace delta
