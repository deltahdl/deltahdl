#include <gtest/gtest.h>

#include "common/arena.h"
#include "simulator/scheduler.h"
#include "simulator/vpi.h"

namespace delta {
namespace {

// A cbEndOfRestart routine that re-establishes the user-data field, which
// §38.33 says an application may do during or after such a callback. The
// handle and the value it associates are file-scope so the routine, whose
// signature the standard fixes, can reach them.
VpiHandle g_restored_call = nullptr;
int g_restored_value = 0;
bool g_restore_ran = false;
int RestoreUserData(VpiCbData*) {
  g_restore_ran = true;
  vpi_put_userdata(g_restored_call, &g_restored_value);
  return 0;
}

class VpiPutUserDataSim : public ::testing::Test {
 protected:
  void SetUp() override {
    g_restored_call = nullptr;
    g_restore_ran = false;
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
  EXPECT_EQ(vpi_get_userdata(call), &marker);
  EXPECT_EQ(vpi_ctx_.LastError().level, 0);
}

// §38.33 (Arguments, edge case): the user-data argument is just a value to be
// associated, so a null value is legal data, not an error. Only the handle is
// validated: putting a null user-data value on a valid call handle still
// succeeds (returns 1), leaving the storage location holding that null value.
TEST_F(VpiPutUserDataSim, NullUserDataValueStillSucceeds) {
  VpiHandle call = MakeCall(vpiSysFuncCall);

  EXPECT_EQ(vpi_put_userdata(call, nullptr), 1);
  EXPECT_EQ(vpi_get_userdata(call), nullptr);
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
  // §38.14 reads the same storage, and a module has none to have been written.
  EXPECT_EQ(vpi_get_userdata(module), nullptr);  // left unassociated
}

// §38.33 (the lone 'shall'): after a restart, a vpi_get_userdata() shall return
// NULL. The user-data association placed before the restart is dropped, so the
// storage location reads back null once the restart sequence has run.
TEST_F(VpiPutUserDataSim, RestartClearsUserData) {
  VpiHandle call = MakeCall(vpiSysFuncCall);
  int marker = 0;
  ASSERT_EQ(vpi_put_userdata(call, &marker), 1);
  ASSERT_EQ(vpi_get_userdata(call), &marker);

  vpi_ctx_.DispatchRestart();

  EXPECT_EQ(vpi_get_userdata(call), nullptr);
}

// §38.33 (the lone 'shall'): a reset clears the user-data association the same
// way a restart does, so a vpi_get_userdata() after the reset yields null.
TEST_F(VpiPutUserDataSim, ResetClearsUserData) {
  VpiHandle call = MakeCall(vpiSysTaskCall);
  int marker = 0;
  ASSERT_EQ(vpi_put_userdata(call, &marker), 1);
  ASSERT_EQ(vpi_get_userdata(call), &marker);

  vpi_ctx_.DispatchReset();

  EXPECT_EQ(vpi_get_userdata(call), nullptr);
}

// §38.33's last sentence: "The user-data field can be set up again during or
// after callbacks of type cbEndOfRestart or cbEndOfReset." A restart clears the
// field before those callbacks run, so a routine that sets it while one is
// being delivered leaves it set afterwards rather than having its write dropped
// by the clear.
TEST_F(VpiPutUserDataSim, TheFieldCanBeSetUpAgainFromAnEndOfRestartCallback) {
  VpiHandle call = MakeCall(vpiSysTaskCall);
  int before_restart = 0;
  ASSERT_EQ(vpi_put_userdata(call, &before_restart), 1);

  g_restored_call = call;
  s_cb_data cb = {};
  cb.reason = cbEndOfRestart;
  cb.cb_rtn = RestoreUserData;
  ASSERT_NE(vpi_register_cb(&cb), nullptr);

  vpi_ctx_.DispatchRestart();

  // The value the callback put there is what a later read finds - not the one
  // from before the restart, which the clear dropped, and not null.
  ASSERT_TRUE(g_restore_ran);
  EXPECT_EQ(vpi_get_userdata(call), &g_restored_value);
  EXPECT_NE(vpi_get_userdata(call), &before_restart);
}

}  // namespace
}  // namespace delta
