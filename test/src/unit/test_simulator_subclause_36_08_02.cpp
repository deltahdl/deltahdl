#include <gtest/gtest.h>

#include <string>

#include "fixture_simulator.h"
#include "simulator/vpi_context.h"
#include "simulator/vpi_data_structs.h"
#include "simulator/vpi_globals.h"
#include "simulator/vpi_internal.h"
#include "simulator/vpi_object.h"
#include "simulator/vpi_user.h"

namespace delta {
namespace {

const char* g_compiletf_arg = nullptr;
int g_compiletf_calls = 0;

PLI_INT32 RecordingCompiletf(PLI_BYTE8* arg) {
  g_compiletf_arg = arg;
  ++g_compiletf_calls;
  return 0;
}

void ResetCompiletfProbe() {
  g_compiletf_arg = nullptr;
  g_compiletf_calls = 0;
}

class CompiletfApplicationRoutine : public ::testing::Test {
 protected:
  void SetUp() override { SetGlobalVpiContext(&vpi_ctx_); }
  void TearDown() override { SetGlobalVpiContext(nullptr); }

  VpiContext vpi_ctx_;
};

TEST_F(CompiletfApplicationRoutine, IsACompileTimeRoutineUnlikeCalltf) {
  EXPECT_TRUE(VpiSystfCallbackFiresAtBuild(VpiSystfCallback::kCompiletf));
  EXPECT_FALSE(VpiSystfCallbackFiresAtBuild(VpiSystfCallback::kCalltf));
}

TEST_F(CompiletfApplicationRoutine, RunsForBothSystemTaskAndSystemFunction) {
  int payload = 0;

  s_vpi_systf_data task = {};
  task.type = kVpiSysTask;
  task.compiletf = &RecordingCompiletf;
  task.user_data = reinterpret_cast<PLI_BYTE8*>(&payload);

  s_vpi_systf_data func = {};
  func.type = kVpiSysFunc;
  func.sysfunctype = kVpiIntFunc;
  func.compiletf = &RecordingCompiletf;
  func.user_data = reinterpret_cast<PLI_BYTE8*>(&payload);

  ResetCompiletfProbe();
  VpiSystfInvoke(task.compiletf, task.user_data);
  EXPECT_EQ(g_compiletf_calls, 1);
  EXPECT_EQ(g_compiletf_arg, reinterpret_cast<const char*>(&payload));

  ResetCompiletfProbe();
  VpiSystfInvoke(func.compiletf, func.user_data);
  EXPECT_EQ(g_compiletf_calls, 1);
  EXPECT_EQ(g_compiletf_arg, reinterpret_cast<const char*>(&payload));
}

TEST_F(CompiletfApplicationRoutine, IsOptional) {
  s_vpi_systf_data no_compiletf = {};
  no_compiletf.type = kVpiSysTask;
  no_compiletf.tfname = VpiText("$check_args");
  no_compiletf.compiletf = nullptr;

  VpiHandle handle = vpi_ctx_.RegisterSystf(&no_compiletf);
  ASSERT_NE(handle, nullptr);

  s_vpi_systf_data read_back = {};
  vpi_ctx_.GetSystfInfo(handle, &read_back);
  EXPECT_EQ(read_back.compiletf, nullptr);

  ResetCompiletfProbe();
  EXPECT_EQ(VpiSystfInvoke(read_back.compiletf, read_back.user_data), 0);
  EXPECT_EQ(g_compiletf_calls, 0);
}

TEST_F(CompiletfApplicationRoutine,
       SuppliedRoutineRoundTripsAndReceivesUserData) {
  int payload = 0;

  s_vpi_systf_data with_compiletf = {};
  with_compiletf.type = kVpiSysFunc;
  with_compiletf.sysfunctype = kVpiIntFunc;
  with_compiletf.tfname = VpiText("$get_vector");
  with_compiletf.compiletf = &RecordingCompiletf;
  with_compiletf.user_data = reinterpret_cast<PLI_BYTE8*>(&payload);

  VpiHandle handle = vpi_ctx_.RegisterSystf(&with_compiletf);
  ASSERT_NE(handle, nullptr);

  s_vpi_systf_data read_back = {};
  vpi_ctx_.GetSystfInfo(handle, &read_back);
  ASSERT_EQ(read_back.compiletf, &RecordingCompiletf);

  ResetCompiletfProbe();
  VpiSystfInvoke(read_back.compiletf, read_back.user_data);
  EXPECT_EQ(g_compiletf_calls, 1);
  EXPECT_EQ(g_compiletf_arg, reinterpret_cast<const char*>(&payload));
}

int g_call_type_seen = 0;
int g_args_seen_at_compile = -1;
std::string g_call_name_seen;
std::string g_systf_name_seen;
std::string g_first_arg_name_seen;

PLI_INT32 InspectingCompiletf(PLI_BYTE8*) {
  g_call_type_seen = 0;
  g_args_seen_at_compile = -1;
  g_call_name_seen.clear();
  g_systf_name_seen.clear();
  g_first_arg_name_seen.clear();

  vpiHandle call = vpi_handle(vpiSysTfCall, nullptr);
  if (call == nullptr) return 0;
  g_call_type_seen = vpi_get(vpiType, call);
  const char* call_name = vpi_get_str(vpiName, call);
  if (call_name != nullptr) g_call_name_seen = call_name;
  vpiHandle systf = vpi_handle(vpiUserSystf, call);
  if (systf != nullptr) {
    s_vpi_systf_data info = {};
    vpi_get_systf_info(systf, &info);
    if (info.tfname != nullptr) g_systf_name_seen = info.tfname;
  }

  vpiHandle args = vpi_iterate(vpiArgument, call);
  g_args_seen_at_compile = 0;
  if (args == nullptr) return 0;
  for (vpiHandle arg = vpi_scan(args); arg != nullptr; arg = vpi_scan(args)) {
    ++g_args_seen_at_compile;
    if (g_args_seen_at_compile != 1) continue;
    const char* arg_name = vpi_get_str(vpiName, arg);
    if (arg_name != nullptr) g_first_arg_name_seen = arg_name;
  }
  return 0;
}

void RegisterInspectingProbe(int type) {
  s_vpi_systf_data data = {};
  data.type = type;
  data.sysfunctype = vpiIntFunc;
  data.tfname = VpiText("$probe");
  data.compiletf = &InspectingCompiletf;
  ASSERT_NE(vpi_register_systf(&data), nullptr);
}

TEST_F(CompiletfApplicationRoutine, ReachesTheCallTheSourceWroteItFor) {
  RegisterInspectingProbe(vpiSysTask);

  SimFixture f;
  auto* design = ElaborateSrc(
      "module t;\n"
      "  int r;\n"
      "  initial $probe(r, 1 + 2);\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  LowerAndRun(design, f);

  EXPECT_EQ(g_call_type_seen, vpiSysTaskCall);
  EXPECT_EQ(g_call_name_seen, "");
  EXPECT_EQ(g_systf_name_seen, "$probe");
  EXPECT_EQ(g_args_seen_at_compile, 2);
  EXPECT_EQ(g_first_arg_name_seen, "r");
}

TEST_F(CompiletfApplicationRoutine, ReachesASystemFunctionCallTheSameWay) {
  RegisterInspectingProbe(vpiSysFunc);

  SimFixture f;
  auto* design = ElaborateSrc(
      "module t;\n"
      "  int r;\n"
      "  initial r = $probe(r);\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  LowerAndRun(design, f);

  EXPECT_EQ(g_call_type_seen, vpiSysFuncCall);
  EXPECT_EQ(g_call_name_seen, "$probe");
  EXPECT_EQ(g_systf_name_seen, "$probe");
  EXPECT_EQ(g_args_seen_at_compile, 1);
  EXPECT_EQ(g_first_arg_name_seen, "r");
}

}  // namespace
}  // namespace delta
