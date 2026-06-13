#include <gtest/gtest.h>

#include "common/arena.h"
#include "simulator/scheduler.h"
#include "simulator/vpi.h"

namespace delta {
namespace {

class VpiGetUserDataSim : public ::testing::Test {
 protected:
  void SetUp() override {
    vpi_ctx_.SetScheduler(&scheduler_);
    SetGlobalVpiContext(&vpi_ctx_);
  }
  void TearDown() override { SetGlobalVpiContext(nullptr); }

  // Build a system task/function call-instance handle of the given type, the
  // kind of handle that owns a user-data storage location.
  VpiHandle MakeCall(int type) {
    VpiHandle obj = vpi_ctx_.CreateModule("c", "c");
    obj->type = type;
    return obj;
  }

  Arena arena_;
  Scheduler scheduler_{arena_};
  VpiContext vpi_ctx_;
};

// §38.14 (the first 'shall'): the routine returns the user-data value a previous
// vpi_put_userdata() associated with the call instance. The pointer read back is
// the very one the application stored.
TEST_F(VpiGetUserDataSim, ReturnsValueAssociatedByPut) {
  VpiHandle call = MakeCall(vpiSysFuncCall);
  int marker = 0;
  ASSERT_EQ(vpi_put_userdata(call, &marker), 1);

  EXPECT_EQ(vpi_get_userdata(call), &marker);
  EXPECT_EQ(vpi_ctx_.LastError().level, 0);
}

// §38.14 (the second 'shall'): when no user data has ever been associated with
// the object, the return value is NULL. The call handle is valid, so this is the
// "no user data" case rather than a failure.
TEST_F(VpiGetUserDataSim, ReturnsNullWhenNothingAssociated) {
  VpiHandle call = MakeCall(vpiSysTaskCall);

  EXPECT_EQ(vpi_get_userdata(call), nullptr);
}

// §38.14 (the second 'shall', failure case): a null handle has no storage
// location to read, so the routine fails and returns NULL, reporting an error
// (§38.2).
TEST_F(VpiGetUserDataSim, ReturnsNullForNullHandle) {
  EXPECT_EQ(vpi_get_userdata(nullptr), nullptr);
  EXPECT_EQ(vpi_ctx_.LastError().level, kVpiError);
}

// §38.14 (the second 'shall', failure case): the handle must name a system
// task/function call instance. A handle of any other kind (here a module) is a
// failure: the routine returns NULL and reports an error.
TEST_F(VpiGetUserDataSim, ReturnsNullForNonCallHandle) {
  VpiHandle module = MakeCall(kVpiModule);

  EXPECT_EQ(vpi_get_userdata(module), nullptr);
  EXPECT_EQ(vpi_ctx_.LastError().level, kVpiError);
}

// §38.14 (the third 'shall'): after a restart, a vpi_get_userdata() returns
// NULL. The association placed before the restart is dropped, so the reader
// yields null once the restart sequence has run.
TEST_F(VpiGetUserDataSim, ReturnsNullAfterRestart) {
  VpiHandle call = MakeCall(vpiSysFuncCall);
  int marker = 0;
  ASSERT_EQ(vpi_put_userdata(call, &marker), 1);
  ASSERT_EQ(vpi_get_userdata(call), &marker);

  vpi_ctx_.DispatchRestart();

  EXPECT_EQ(vpi_get_userdata(call), nullptr);
}

}  // namespace
}  // namespace delta
