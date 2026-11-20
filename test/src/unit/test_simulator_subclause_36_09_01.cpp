#include <gtest/gtest.h>

#include "fixture_simulator.h"
#include "simulator/vpi_context.h"
#include "simulator/vpi_globals.h"
#include "simulator/vpi_internal.h"
#include "simulator/vpi_user.h"

namespace delta {
namespace {

class UserDefinedSystfRegistration : public ::testing::Test {
 protected:
  void SetUp() override { SetGlobalVpiContext(&vpi_ctx_); }
  void TearDown() override { SetGlobalVpiContext(nullptr); }

  VpiContext vpi_ctx_;
};

TEST_F(UserDefinedSystfRegistration, NameWithoutDollarIsRejected) {
  s_vpi_systf_data data = {};
  data.type = vpiSysTask;
  data.tfname = VpiText("missing_dollar");

  vpiHandle h = vpi_register_systf(&data);

  EXPECT_EQ(h, nullptr);
  EXPECT_TRUE(vpi_ctx_.RegisteredSystfs().empty());
}

TEST_F(UserDefinedSystfRegistration, NameWithDollarIsAccepted) {
  s_vpi_systf_data data = {};
  data.type = vpiSysTask;
  data.tfname = VpiText("$get_vector");

  vpiHandle h = vpi_register_systf(&data);

  ASSERT_NE(h, nullptr);
  ASSERT_EQ(vpi_ctx_.RegisteredSystfs().size(), 1);
  EXPECT_STREQ(vpi_ctx_.RegisteredSystfs()[0].tfname, "$get_vector");
}

TEST_F(UserDefinedSystfRegistration, NullNameIsRejected) {
  s_vpi_systf_data data = {};
  data.type = vpiSysFunc;
  data.sysfunctype = vpiIntFunc;
  data.tfname = nullptr;

  vpiHandle h = vpi_register_systf(&data);

  EXPECT_EQ(h, nullptr);
  EXPECT_TRUE(vpi_ctx_.RegisteredSystfs().empty());
}

TEST_F(UserDefinedSystfRegistration, RegistrationBeforeElaborationSucceeds) {
  s_vpi_systf_data data = {};
  data.type = vpiSysTask;
  data.tfname = VpiText("$early");

  vpiHandle h = vpi_register_systf(&data);

  ASSERT_NE(h, nullptr);
  EXPECT_EQ(vpi_ctx_.RegisteredSystfs().size(), 1);
}

TEST_F(UserDefinedSystfRegistration, RegistrationAfterElaborationIsRejected) {
  vpi_ctx_.MarkElaborationStarted();

  s_vpi_systf_data data = {};
  data.type = vpiSysTask;
  data.tfname = VpiText("$late");

  vpiHandle h = vpi_register_systf(&data);
  s_vpi_error_info info = {};
  const PLI_INT32 kLevel = vpi_chk_error(&info);

  EXPECT_EQ(h, nullptr);
  EXPECT_TRUE(vpi_ctx_.RegisteredSystfs().empty());
  EXPECT_EQ(kLevel, vpiError);
  EXPECT_EQ(info.level, vpiError);
  EXPECT_EQ(info.state, vpiPLI);
}

TEST_F(UserDefinedSystfRegistration, FunctionNameWithoutDollarIsRejected) {
  s_vpi_systf_data data = {};
  data.type = vpiSysFunc;
  data.sysfunctype = vpiIntFunc;
  data.tfname = VpiText("get_vector");

  vpiHandle h = vpi_register_systf(&data);
  s_vpi_error_info info = {};
  const PLI_INT32 kLevel = vpi_chk_error(&info);

  EXPECT_EQ(h, nullptr);
  EXPECT_TRUE(vpi_ctx_.RegisteredSystfs().empty());
  EXPECT_EQ(kLevel, vpiError);
}

TEST_F(UserDefinedSystfRegistration, FunctionNameWithDollarIsAccepted) {
  s_vpi_systf_data data = {};
  data.type = vpiSysFunc;
  data.sysfunctype = vpiIntFunc;
  data.tfname = VpiText("$get_vector");

  vpiHandle h = vpi_register_systf(&data);

  ASSERT_NE(h, nullptr);
  ASSERT_EQ(vpi_ctx_.RegisteredSystfs().size(), 1);
  EXPECT_STREQ(vpi_ctx_.RegisteredSystfs()[0].tfname, "$get_vector");
  EXPECT_EQ(vpi_ctx_.RegisteredSystfs()[0].type, vpiSysFunc);
}

TEST_F(UserDefinedSystfRegistration,
       RegistrationDistinguishesFunctionFromTask) {
  s_vpi_systf_data task = {};
  task.type = vpiSysTask;
  task.tfname = VpiText("$as_task");

  s_vpi_systf_data func = {};
  func.type = vpiSysFunc;
  func.sysfunctype = vpiIntFunc;
  func.tfname = VpiText("$as_func");

  ASSERT_NE(vpi_register_systf(&task), nullptr);
  ASSERT_NE(vpi_register_systf(&func), nullptr);

  ASSERT_EQ(vpi_ctx_.RegisteredSystfs().size(), 2);
  EXPECT_EQ(vpi_ctx_.RegisteredSystfs()[0].type, vpiSysTask);
  EXPECT_EQ(vpi_ctx_.RegisteredSystfs()[1].type, vpiSysFunc);
}

namespace {

void StartupRoutineRegistersTask() {
  s_vpi_systf_data data = {};
  data.type = vpiSysTask;
  data.tfname = VpiText("$startup_task");
  vpi_register_systf(&data);
}

void StartupRoutineRegistersFunc() {
  s_vpi_systf_data data = {};
  data.type = vpiSysFunc;
  data.sysfunctype = vpiIntFunc;
  data.tfname = VpiText("$startup_func");
  vpi_register_systf(&data);
}

}  // namespace

TEST_F(UserDefinedSystfRegistration,
       VlogStartupRoutinesArrayInvokesEachRoutine) {
  VlogStartupRoutine routines[] = {
      &StartupRoutineRegistersTask,
      &StartupRoutineRegistersFunc,
      nullptr,
  };

  InvokeVlogStartupRoutines(routines);

  ASSERT_EQ(vpi_ctx_.RegisteredSystfs().size(), 2);
  EXPECT_STREQ(vpi_ctx_.RegisteredSystfs()[0].tfname, "$startup_task");
  EXPECT_STREQ(vpi_ctx_.RegisteredSystfs()[1].tfname, "$startup_func");
}

TEST_F(UserDefinedSystfRegistration, VlogStartupRoutinesStopAtNullSentinel) {
  VlogStartupRoutine routines[] = {
      &StartupRoutineRegistersTask,
      nullptr,
      &StartupRoutineRegistersFunc,
  };

  InvokeVlogStartupRoutines(routines);

  ASSERT_EQ(vpi_ctx_.RegisteredSystfs().size(), 1);
  EXPECT_STREQ(vpi_ctx_.RegisteredSystfs()[0].tfname, "$startup_task");
}

bool g_late_tried = false;
vpiHandle g_late_handle = nullptr;
PLI_INT32 g_late_level = 0;
PLI_INT32 g_late_state = 0;

void TryALateRegistration() {
  s_vpi_systf_data data = {};
  data.type = vpiSysTask;
  data.tfname = VpiText("$late");
  vpiHandle h = vpi_register_systf(&data);
  s_vpi_error_info info = {};
  const PLI_INT32 kLevel = vpi_chk_error(&info);
  g_late_tried = true;
  g_late_handle = h;
  g_late_level = kLevel;
  g_late_state = info.state;
}

PLI_INT32 LateFromACallback(p_cb_data) {
  TryALateRegistration();
  return 0;
}

PLI_INT32 LateFromARoutine(PLI_BYTE8*) {
  TryALateRegistration();
  return 0;
}

PLI_INT32 LateFromASizetf(PLI_BYTE8*) {
  TryALateRegistration();
  return 32;
}

class LateSystfRegistration : public ::testing::Test {
 protected:
  void SetUp() override {
    g_late_tried = false;
    g_late_handle = nullptr;
    g_late_level = 0;
    g_late_state = 0;
    SetGlobalVpiContext(&vpi_ctx_);
  }
  void TearDown() override { SetGlobalVpiContext(nullptr); }

  void RegisterTheCallback(PLI_INT32 reason) {
    s_cb_data cb = {};
    cb.reason = reason;
    cb.cb_rtn = &LateFromACallback;
    ASSERT_NE(vpi_register_cb(&cb), nullptr);
  }

  void RunWith(PLI_INT32 (*sizetf)(PLI_BYTE8*),
               PLI_INT32 (*compiletf)(PLI_BYTE8*),
               PLI_INT32 (*calltf)(PLI_BYTE8*)) {
    s_vpi_systf_data data = {};
    data.type = vpiSysFunc;
    data.sysfunctype = vpiSizedFunc;
    data.tfname = VpiText("$probe");
    data.sizetf = sizetf;
    data.compiletf = compiletf;
    data.calltf = calltf;
    ASSERT_NE(vpi_register_systf(&data), nullptr);
    SimFixture f;
    auto* design = ElaborateSrc(
        "module t;\n"
        "  int r;\n"
        "  initial r = $probe();\n"
        "endmodule\n",
        f);
    ASSERT_NE(design, nullptr);
    LowerAndRun(design, f);
  }

  void ExpectTheLateRegistrationRefused() {
    ASSERT_TRUE(g_late_tried);
    EXPECT_EQ(g_late_handle, nullptr);
    EXPECT_EQ(g_late_level, vpiError);
    EXPECT_EQ(g_late_state, vpiPLI);
    ASSERT_EQ(vpi_ctx_.RegisteredSystfs().size(), 1);
    EXPECT_STREQ(vpi_ctx_.RegisteredSystfs()[0].tfname, "$probe");
  }

  VpiContext vpi_ctx_;
};

TEST_F(LateSystfRegistration, DISABLED_ARegistrationFromASizetfIsRefused) {
  RunWith(&LateFromASizetf, nullptr, nullptr);
  ExpectTheLateRegistrationRefused();
}

TEST_F(LateSystfRegistration, DISABLED_ARegistrationFromACompiletfIsRefused) {
  RunWith(nullptr, &LateFromARoutine, nullptr);
  ExpectTheLateRegistrationRefused();
}

TEST_F(LateSystfRegistration, DISABLED_ARegistrationFromACalltfIsRefused) {
  RunWith(nullptr, nullptr, &LateFromARoutine);
  ExpectTheLateRegistrationRefused();
}

TEST_F(LateSystfRegistration,
       DISABLED_ARegistrationAtTheEndOfCompileIsRefused) {
  RegisterTheCallback(cbEndOfCompile);
  RunWith(nullptr, nullptr, nullptr);
  ExpectTheLateRegistrationRefused();
}

TEST_F(LateSystfRegistration,
       DISABLED_ARegistrationAtTheStartOfSimulationIsRefused) {
  RegisterTheCallback(cbStartOfSimulation);
  RunWith(nullptr, nullptr, nullptr);
  ExpectTheLateRegistrationRefused();
}

}  // namespace
}  // namespace delta
