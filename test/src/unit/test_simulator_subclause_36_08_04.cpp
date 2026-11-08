#include <gtest/gtest.h>

#include "fixture_simulator.h"
#include "simulator/vpi_context.h"
#include "simulator/vpi_data_structs.h"
#include "simulator/vpi_globals.h"
#include "simulator/vpi_internal.h"
#include "simulator/vpi_object.h"
#include "simulator/vpi_user.h"

namespace delta {
namespace {

const char* g_sizetf_arg = nullptr;
const char* g_compiletf_arg = nullptr;
const char* g_calltf_arg = nullptr;

PLI_INT32 RecordingSizetf(PLI_BYTE8* arg) {
  g_sizetf_arg = arg;
  return 0;
}

PLI_INT32 RecordingCompiletf(PLI_BYTE8* arg) {
  g_compiletf_arg = arg;
  return 0;
}

PLI_INT32 RecordingCalltf(PLI_BYTE8* arg) {
  g_calltf_arg = arg;
  return 0;
}

void ResetArgProbes() {
  g_sizetf_arg = nullptr;
  g_compiletf_arg = nullptr;
  g_calltf_arg = nullptr;
}

class SystfApplicationRoutineArguments : public ::testing::Test {
 protected:
  void SetUp() override { SetGlobalVpiContext(&vpi_ctx_); }
  void TearDown() override { SetGlobalVpiContext(nullptr); }

  VpiContext vpi_ctx_;
};

TEST_F(SystfApplicationRoutineArguments,
       AllThreeRoutinesTakeTheOneUserDataArgument) {
  int payload = 0;

  s_vpi_systf_data data = {};
  data.type = kVpiSysFunc;
  data.sysfunctype = kVpiSizedFunc;
  data.tfname = VpiText("$probe");
  data.sizetf = &RecordingSizetf;
  data.compiletf = &RecordingCompiletf;
  data.calltf = &RecordingCalltf;
  data.user_data = reinterpret_cast<PLI_BYTE8*>(&payload);

  ResetArgProbes();
  VpiSystfInvoke(data.sizetf, data.user_data);
  VpiSystfInvoke(data.compiletf, data.user_data);
  VpiSystfInvoke(data.calltf, data.user_data);

  const char* expected = reinterpret_cast<const char*>(&payload);
  EXPECT_EQ(g_sizetf_arg, expected);
  EXPECT_EQ(g_compiletf_arg, expected);
  EXPECT_EQ(g_calltf_arg, expected);
}

TEST_F(SystfApplicationRoutineArguments,
       RegisteredUserDataIsPassedToEachRoutine) {
  int payload = 0;

  s_vpi_systf_data data = {};
  data.type = kVpiSysFunc;
  data.sysfunctype = kVpiSizedFunc;
  data.tfname = VpiText("$probe");
  data.sizetf = &RecordingSizetf;
  data.compiletf = &RecordingCompiletf;
  data.calltf = &RecordingCalltf;
  data.user_data = reinterpret_cast<PLI_BYTE8*>(&payload);

  VpiHandle handle = vpi_ctx_.RegisterSystf(&data);
  ASSERT_NE(handle, nullptr);

  s_vpi_systf_data read_back = {};
  vpi_ctx_.GetSystfInfo(handle, &read_back);
  ASSERT_EQ(read_back.user_data, reinterpret_cast<PLI_BYTE8*>(&payload));

  ResetArgProbes();
  VpiSystfInvoke(read_back.sizetf, read_back.user_data);
  VpiSystfInvoke(read_back.compiletf, read_back.user_data);
  VpiSystfInvoke(read_back.calltf, read_back.user_data);

  const char* expected = reinterpret_cast<const char*>(&payload);
  EXPECT_EQ(g_sizetf_arg, expected);
  EXPECT_EQ(g_compiletf_arg, expected);
  EXPECT_EQ(g_calltf_arg, expected);
}

TEST_F(SystfApplicationRoutineArguments,
       EachRegistrationSuppliesItsOwnUserData) {
  int payload_a = 0;
  int payload_b = 0;

  s_vpi_systf_data task = {};
  task.type = kVpiSysTask;
  task.calltf = &RecordingCalltf;
  task.user_data = reinterpret_cast<PLI_BYTE8*>(&payload_a);

  s_vpi_systf_data func = {};
  func.type = kVpiSysFunc;
  func.sysfunctype = kVpiIntFunc;
  func.calltf = &RecordingCalltf;
  func.user_data = reinterpret_cast<PLI_BYTE8*>(&payload_b);

  ResetArgProbes();
  VpiSystfInvoke(task.calltf, task.user_data);
  EXPECT_EQ(g_calltf_arg, reinterpret_cast<const char*>(&payload_a));

  ResetArgProbes();
  VpiSystfInvoke(func.calltf, func.user_data);
  EXPECT_EQ(g_calltf_arg, reinterpret_cast<const char*>(&payload_b));
}

TEST_F(SystfApplicationRoutineArguments, NullUserDataIsPassedThroughUnchanged) {
  s_vpi_systf_data data = {};
  data.type = kVpiSysFunc;
  data.sysfunctype = kVpiSizedFunc;
  data.sizetf = &RecordingSizetf;
  data.compiletf = &RecordingCompiletf;
  data.calltf = &RecordingCalltf;
  data.user_data = nullptr;

  ResetArgProbes();
  VpiSystfInvoke(data.sizetf, data.user_data);
  VpiSystfInvoke(data.compiletf, data.user_data);
  VpiSystfInvoke(data.calltf, data.user_data);

  EXPECT_EQ(g_sizetf_arg, nullptr);
  EXPECT_EQ(g_compiletf_arg, nullptr);
  EXPECT_EQ(g_calltf_arg, nullptr);
}

char g_registered_user_data[] = "vector-reader";

const char* g_run_sizetf_arg = nullptr;
const char* g_run_compiletf_arg = nullptr;
const char* g_run_calltf_arg = nullptr;
bool g_run_sizetf_ran = false;
bool g_run_compiletf_ran = false;
bool g_run_calltf_ran = false;

PLI_INT32 RunSizetf(PLI_BYTE8* arg) {
  g_run_sizetf_arg = arg;
  g_run_sizetf_ran = true;
  return 8;
}

PLI_INT32 RunCompiletf(PLI_BYTE8* arg) {
  g_run_compiletf_arg = arg;
  g_run_compiletf_ran = true;
  return 0;
}

PLI_INT32 RunCalltf(PLI_BYTE8* arg) {
  g_run_calltf_arg = arg;
  g_run_calltf_ran = true;
  return 0;
}

void ResetRunProbes() {
  g_run_sizetf_arg = nullptr;
  g_run_compiletf_arg = nullptr;
  g_run_calltf_arg = nullptr;
  g_run_sizetf_ran = false;
  g_run_compiletf_ran = false;
  g_run_calltf_ran = false;
}

s_vpi_systf_data ProbeRegistration(void* user_data) {
  s_vpi_systf_data data = {};
  data.type = vpiSysFunc;
  data.sysfunctype = vpiSizedFunc;
  data.tfname = VpiText("$probe");
  data.sizetf = &RunSizetf;
  data.compiletf = &RunCompiletf;
  data.calltf = &RunCalltf;
  data.user_data = static_cast<PLI_BYTE8*>(user_data);
  return data;
}

void RunOneProbeCall(SimFixture& f) {
  auto* design = ElaborateSrc(
      "module t;\n"
      "  int r;\n"
      "  initial r = $probe();\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  LowerAndRun(design, f);
}

TEST_F(SystfApplicationRoutineArguments,
       TheToolHandsEachRoutineTheRegisteredUserData) {
  ResetRunProbes();
  s_vpi_systf_data data = ProbeRegistration(g_registered_user_data);
  ASSERT_NE(vpi_register_systf(&data), nullptr);

  SimFixture f;
  RunOneProbeCall(f);

  ASSERT_TRUE(g_run_sizetf_ran);
  ASSERT_TRUE(g_run_compiletf_ran);
  ASSERT_TRUE(g_run_calltf_ran);
  EXPECT_EQ(g_run_sizetf_arg, g_registered_user_data);
  EXPECT_EQ(g_run_compiletf_arg, g_registered_user_data);
  EXPECT_EQ(g_run_calltf_arg, g_registered_user_data);
}

TEST_F(SystfApplicationRoutineArguments,
       TheValueIsTheOneThatStoodAtRegistration) {
  char later_user_data[] = "written-afterwards";
  ResetRunProbes();
  s_vpi_systf_data data = ProbeRegistration(g_registered_user_data);
  ASSERT_NE(vpi_register_systf(&data), nullptr);
  data.user_data = later_user_data;

  SimFixture f;
  RunOneProbeCall(f);

  EXPECT_EQ(g_run_sizetf_arg, g_registered_user_data);
  EXPECT_EQ(g_run_compiletf_arg, g_registered_user_data);
  EXPECT_EQ(g_run_calltf_arg, g_registered_user_data);
}

TEST_F(SystfApplicationRoutineArguments,
       TheToolHandsThroughANullUserDataUnchanged) {
  ResetRunProbes();
  s_vpi_systf_data data = ProbeRegistration(nullptr);
  ASSERT_NE(vpi_register_systf(&data), nullptr);

  SimFixture f;
  RunOneProbeCall(f);

  ASSERT_TRUE(g_run_sizetf_ran);
  ASSERT_TRUE(g_run_compiletf_ran);
  ASSERT_TRUE(g_run_calltf_ran);
  EXPECT_EQ(g_run_sizetf_arg, nullptr);
  EXPECT_EQ(g_run_compiletf_arg, nullptr);
  EXPECT_EQ(g_run_calltf_arg, nullptr);
}

}  // namespace
}  // namespace delta
