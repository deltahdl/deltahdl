#include <gtest/gtest.h>

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

  EXPECT_EQ(h, nullptr);
  EXPECT_TRUE(vpi_ctx_.RegisteredSystfs().empty());
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

}  // namespace
}  // namespace delta
