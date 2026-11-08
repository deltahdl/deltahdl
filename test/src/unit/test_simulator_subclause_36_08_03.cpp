#include <gtest/gtest.h>

#include <cstdint>

#include "fixture_simulator.h"
#include "simulator/vpi_context.h"
#include "simulator/vpi_data_structs.h"
#include "simulator/vpi_globals.h"
#include "simulator/vpi_internal.h"
#include "simulator/vpi_object.h"
#include "simulator/vpi_user.h"

namespace delta {
namespace {

const char* g_calltf_arg = nullptr;
int g_calltf_calls = 0;

PLI_INT32 RecordingCalltf(PLI_BYTE8* arg) {
  g_calltf_arg = arg;
  ++g_calltf_calls;
  return 0;
}

void ResetCalltfProbe() {
  g_calltf_arg = nullptr;
  g_calltf_calls = 0;
}

class CalltfApplicationRoutine : public ::testing::Test {
 protected:
  void SetUp() override { SetGlobalVpiContext(&vpi_ctx_); }
  void TearDown() override { SetGlobalVpiContext(nullptr); }

  VpiContext vpi_ctx_;
};

TEST_F(CalltfApplicationRoutine, RunsAtExecutionTimeNotAtBuild) {
  EXPECT_FALSE(VpiSystfCallbackFiresAtBuild(VpiSystfCallback::kCalltf));
}

TEST_F(CalltfApplicationRoutine, IsCalledOncePerExecution) {
  int payload = 0;

  s_vpi_systf_data get_vector = {};
  get_vector.type = kVpiSysTask;
  get_vector.tfname = VpiText("$get_vector");
  get_vector.calltf = &RecordingCalltf;
  get_vector.user_data = reinterpret_cast<PLI_BYTE8*>(&payload);

  ResetCalltfProbe();
  const int kExecutions = 1024;
  for (int i = 0; i < kExecutions; ++i) {
    VpiSystfInvoke(get_vector.calltf, get_vector.user_data);
  }
  EXPECT_EQ(g_calltf_calls, kExecutions);
  EXPECT_EQ(g_calltf_arg, reinterpret_cast<const char*>(&payload));
}

TEST_F(CalltfApplicationRoutine, RunsForBothSystemTaskAndSystemFunction) {
  int payload = 0;

  s_vpi_systf_data task = {};
  task.type = kVpiSysTask;
  task.calltf = &RecordingCalltf;
  task.user_data = reinterpret_cast<PLI_BYTE8*>(&payload);

  s_vpi_systf_data func = {};
  func.type = kVpiSysFunc;
  func.sysfunctype = kVpiIntFunc;
  func.calltf = &RecordingCalltf;
  func.user_data = reinterpret_cast<PLI_BYTE8*>(&payload);

  ResetCalltfProbe();
  VpiSystfInvoke(task.calltf, task.user_data);
  EXPECT_EQ(g_calltf_calls, 1);
  EXPECT_EQ(g_calltf_arg, reinterpret_cast<const char*>(&payload));

  ResetCalltfProbe();
  VpiSystfInvoke(func.calltf, func.user_data);
  EXPECT_EQ(g_calltf_calls, 1);
  EXPECT_EQ(g_calltf_arg, reinterpret_cast<const char*>(&payload));
}

TEST_F(CalltfApplicationRoutine, SuppliedRoutineRoundTripsAndReceivesUserData) {
  int payload = 0;

  s_vpi_systf_data with_calltf = {};
  with_calltf.type = kVpiSysFunc;
  with_calltf.sysfunctype = kVpiIntFunc;
  with_calltf.tfname = VpiText("$get_vector");
  with_calltf.calltf = &RecordingCalltf;
  with_calltf.user_data = reinterpret_cast<PLI_BYTE8*>(&payload);

  VpiHandle handle = vpi_ctx_.RegisterSystf(&with_calltf);
  ASSERT_NE(handle, nullptr);

  s_vpi_systf_data read_back = {};
  vpi_ctx_.GetSystfInfo(handle, &read_back);
  ASSERT_EQ(read_back.calltf, &RecordingCalltf);

  ResetCalltfProbe();
  VpiSystfInvoke(read_back.calltf, read_back.user_data);
  EXPECT_EQ(g_calltf_calls, 1);
  EXPECT_EQ(g_calltf_arg, reinterpret_cast<const char*>(&payload));
}

int g_calltf_runs = 0;
int g_compiletf_runs = 0;
uint64_t g_arg_total = 0;

PLI_INT32 CountingCalltf(PLI_BYTE8*) {
  ++g_calltf_runs;
  vpiHandle call = vpi_handle(vpiSysTfCall, nullptr);
  if (call == nullptr) return 0;
  vpiHandle args = vpi_iterate(vpiArgument, call);
  if (args == nullptr) return 0;
  vpiHandle arg = vpi_scan(args);
  if (arg == nullptr) return 0;
  s_vpi_value value = {};
  value.format = vpiIntVal;
  vpi_get_value(arg, &value);
  g_arg_total += static_cast<uint64_t>(value.value.integer);
  return 0;
}

PLI_INT32 CountingCompiletf(PLI_BYTE8*) {
  ++g_compiletf_runs;
  return 0;
}

void RegisterCountingProbe() {
  g_calltf_runs = 0;
  g_compiletf_runs = 0;
  g_arg_total = 0;
  s_vpi_systf_data data = {};
  data.type = vpiSysTask;
  data.tfname = VpiText("$probe");
  data.calltf = &CountingCalltf;
  data.compiletf = &CountingCompiletf;
  ASSERT_NE(vpi_register_systf(&data), nullptr);
}

TEST_F(CalltfApplicationRoutine, RunsOncePerExecutionOfTheOneCallSite) {
  RegisterCountingProbe();

  SimFixture f;
  auto* design = ElaborateSrc(
      "module t;\n"
      "  int i;\n"
      "  initial for (i = 1; i <= 4; i = i + 1) $probe(i);\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  LowerAndRun(design, f);

  EXPECT_EQ(g_calltf_runs, 4);
  EXPECT_EQ(g_compiletf_runs, 1);
}

TEST_F(CalltfApplicationRoutine, ReadsTheArgumentsAsTheyStandAtEachExecution) {
  RegisterCountingProbe();

  SimFixture f;
  auto* design = ElaborateSrc(
      "module t;\n"
      "  int i;\n"
      "  initial for (i = 1; i <= 4; i = i + 1) $probe(i);\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  LowerAndRun(design, f);

  EXPECT_EQ(g_arg_total, 10u);
}

TEST_F(CalltfApplicationRoutine, RunsAgainAtEveryLaterTimeTheCallIsReached) {
  RegisterCountingProbe();

  SimFixture f;
  auto* design = ElaborateSrc(
      "module t;\n"
      "  int i;\n"
      "  initial for (i = 1; i <= 3; i = i + 1) #5 $probe(i);\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  LowerAndRun(design, f);

  EXPECT_EQ(g_calltf_runs, 3);
  EXPECT_EQ(g_arg_total, 6u);
  EXPECT_EQ(g_compiletf_runs, 1);
}

}  // namespace
}  // namespace delta
