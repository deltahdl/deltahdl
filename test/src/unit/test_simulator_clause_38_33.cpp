#include <gtest/gtest.h>

#include "common/arena.h"
#include "simulator/scheduler.h"
#include "simulator/vpi.h"

namespace delta {
namespace {

class VpiPutUserDataSim : public ::testing::Test {
 protected:
  void SetUp() override {
    vpi_ctx_.SetScheduler(&scheduler_);
    SetGlobalVpiContext(&vpi_ctx_);
  }
  void TearDown() override { SetGlobalVpiContext(nullptr); }

  // Build a system task/function call-instance handle of the given type. The
  // handle is a VpiObject*, so the test reads the storage location
  // vpi_put_userdata() writes (obj->user_data) back directly.
  VpiHandle MakeCall(int type) {
    VpiHandle obj = vpi_ctx_.CreateModule("c", "c");
    obj->type = type;
    return obj;
  }

  Arena arena_;
  Scheduler scheduler_{arena_};
  VpiContext vpi_ctx_;
};

// §38.33 (Synopsis/Arguments + Returns): vpi_put_userdata() associates the
// user-data value with a system function call instance's storage location and
// returns 1 on success. The stored pointer is the one the application supplied.
TEST_F(VpiPutUserDataSim, AssociatesUserDataWithFunctionCall) {
  VpiHandle call = MakeCall(vpiSysFuncCall);
  int marker = 0;

  EXPECT_EQ(vpi_put_userdata(call, &marker), 1);
  EXPECT_EQ(call->user_data, &marker);
  EXPECT_EQ(vpi_ctx_.LastError().level, 0);
}

// §38.33 (Arguments): the routine also accepts a system task call instance -
// the other call kind the routine names - storing and returning success.
TEST_F(VpiPutUserDataSim, AssociatesUserDataWithTaskCall) {
  VpiHandle call = MakeCall(vpiSysTaskCall);
  int marker = 0;

  EXPECT_EQ(vpi_put_userdata(call, &marker), 1);
  EXPECT_EQ(call->user_data, &marker);
}

// §38.33 (Arguments, edge case): the user-data argument is just a value to be
// associated, so a null value is legal data, not an error. Only the handle is
// validated: putting a null user-data value on a valid call handle still
// succeeds (returns 1), leaving the storage location holding that null value.
TEST_F(VpiPutUserDataSim, NullUserDataValueStillSucceeds) {
  VpiHandle call = MakeCall(vpiSysFuncCall);

  EXPECT_EQ(vpi_put_userdata(call, nullptr), 1);
  EXPECT_EQ(call->user_data, nullptr);
  EXPECT_EQ(vpi_ctx_.LastError().level, 0);
}

// §38.33 (Returns + Arguments): a null handle has no storage location to write,
// so the routine reports an error (§38.2) and returns 0.
TEST_F(VpiPutUserDataSim, NullHandleIsAnError) {
  int marker = 0;

  EXPECT_EQ(vpi_put_userdata(nullptr, &marker), 0);
  EXPECT_EQ(vpi_ctx_.LastError().level, kVpiError);
}

// §38.33 (Returns + Arguments): the handle must name a system task/function
// call instance. A handle of any other kind (here a module) is rejected with an
// error and 0, and no association is made on it.
TEST_F(VpiPutUserDataSim, NonCallHandleIsRejected) {
  VpiHandle module = MakeCall(kVpiModule);
  int marker = 0;

  EXPECT_EQ(vpi_put_userdata(module, &marker), 0);
  EXPECT_EQ(vpi_ctx_.LastError().level, kVpiError);
  EXPECT_EQ(module->user_data, nullptr);  // left unassociated
}

// §38.33 (the lone 'shall'): after a restart, a vpi_get_userdata() shall return
// NULL. The user-data association placed before the restart is dropped, so the
// storage location reads back null once the restart sequence has run.
TEST_F(VpiPutUserDataSim, RestartClearsUserData) {
  VpiHandle call = MakeCall(vpiSysFuncCall);
  int marker = 0;
  ASSERT_EQ(vpi_put_userdata(call, &marker), 1);
  ASSERT_EQ(call->user_data, &marker);

  vpi_ctx_.DispatchRestart();

  EXPECT_EQ(call->user_data, nullptr);
}

// §38.33 (the lone 'shall'): a reset clears the user-data association the same
// way a restart does, so a vpi_get_userdata() after the reset yields null.
TEST_F(VpiPutUserDataSim, ResetClearsUserData) {
  VpiHandle call = MakeCall(vpiSysTaskCall);
  int marker = 0;
  ASSERT_EQ(vpi_put_userdata(call, &marker), 1);
  ASSERT_EQ(call->user_data, &marker);

  vpi_ctx_.DispatchReset();

  EXPECT_EQ(call->user_data, nullptr);
}

}  // namespace
}  // namespace delta
