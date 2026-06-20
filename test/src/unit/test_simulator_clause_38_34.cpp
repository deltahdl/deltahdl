#include <gtest/gtest.h>

#include "common/arena.h"
#include "common/diagnostic.h"
#include "common/source_mgr.h"
#include "simulator/net.h"
#include "simulator/sim_context.h"
#include "simulator/vpi.h"

namespace delta {
namespace {

class VpiPutValueSim : public ::testing::Test {
 protected:
  void SetUp() override { SetGlobalVpiContext(&vpi_ctx_); }
  void TearDown() override { SetGlobalVpiContext(nullptr); }

  SourceManager mgr_;
  Arena arena_;
  Scheduler scheduler_{arena_};
  DiagEngine diag_{mgr_};
  SimContext sim_ctx_{scheduler_, arena_, diag_};
  VpiContext vpi_ctx_;
};

// §38.34: vpiNoDelay sets the object to the passed value immediately. With no
// vpiReturnEvent bit and no delay, the return value is NULL.
TEST_F(VpiPutValueSim, PutValueNoDelay) {
  auto* var = sim_ctx_.CreateVariable("d", 32);
  var->value = MakeLogic4VecVal(arena_, 32, 0);
  vpi_ctx_.Attach(sim_ctx_);

  vpiHandle h = vpi_handle_by_name("d", nullptr);
  ASSERT_NE(h, nullptr);

  s_vpi_value val = {};
  val.format = vpiIntVal;
  val.value.integer = 77;
  vpiHandle ret = vpi_put_value(h, &val, nullptr, vpiNoDelay);
  EXPECT_EQ(ret, nullptr);
  EXPECT_EQ(var->value.ToUint64(), 77u);
}

// §38.34: a put with vpiInertialDelay applies the value to the object.
TEST_F(VpiPutValueSim, PutValueInertialDelay) {
  auto* var = sim_ctx_.CreateVariable("di", 32);
  var->value = MakeLogic4VecVal(arena_, 32, 0);
  vpi_ctx_.Attach(sim_ctx_);

  vpiHandle h = vpi_handle_by_name("di", nullptr);
  s_vpi_value val = {};
  val.format = vpiIntVal;
  val.value.integer = 88;
  s_vpi_time time = {};
  time.type = vpiSimTime;
  time.low = 10;
  vpi_put_value(h, &val, &time, vpiInertialDelay);

  EXPECT_EQ(var->value.ToUint64(), 88u);
}

// §38.34: a value supplied in vpiRealVal format is accepted.
TEST_F(VpiPutValueSim, PutValueRealFormat) {
  auto* var = sim_ctx_.CreateVariable("rf", 32);
  var->value = MakeLogic4VecVal(arena_, 32, 0);
  vpi_ctx_.Attach(sim_ctx_);

  vpiHandle h = vpi_handle_by_name("rf", nullptr);
  s_vpi_value val = {};
  val.format = vpiRealVal;
  val.value.real = 7.0;
  vpi_put_value(h, &val, nullptr, vpiNoDelay);
  EXPECT_EQ(var->value.ToUint64(), 7u);
}

// §38.34: a value supplied in vpiScalarVal format is accepted on a one-bit
// object.
TEST_F(VpiPutValueSim, PutValueScalarFormat) {
  auto* var = sim_ctx_.CreateVariable("sf", 1);
  var->value = MakeLogic4VecVal(arena_, 1, 0);
  vpi_ctx_.Attach(sim_ctx_);

  vpiHandle h = vpi_handle_by_name("sf", nullptr);
  s_vpi_value val = {};
  val.format = vpiScalarVal;
  val.value.scalar = vpi1;
  vpi_put_value(h, &val, nullptr, vpiNoDelay);
  EXPECT_EQ(var->value.words[0].aval & 1, 1u);
  EXPECT_EQ(var->value.words[0].bval & 1, 0u);
}

// §38.34: when vpiReturnEvent is set together with a delay that schedules an
// event, the routine returns a handle of type vpiSchedEvent for that event, and
// the event reports itself as scheduled.
TEST_F(VpiPutValueSim, ReturnEventWithDelayReturnsSchedEventHandle) {
  auto* var = sim_ctx_.CreateVariable("re", 32);
  var->value = MakeLogic4VecVal(arena_, 32, 0);
  vpi_ctx_.Attach(sim_ctx_);

  vpiHandle h = vpi_handle_by_name("re", nullptr);
  s_vpi_value val = {};
  val.format = vpiIntVal;
  val.value.integer = 12;
  s_vpi_time time = {};
  time.type = vpiSimTime;
  time.low = 5;
  vpiHandle ev =
      vpi_put_value(h, &val, &time, vpiInertialDelay | vpiReturnEvent);
  ASSERT_NE(ev, nullptr);
  EXPECT_EQ(vpi_get(vpiType, ev), vpiSchedEvent);
  EXPECT_EQ(vpi_get(vpiScheduled, ev), 1);
}

// §38.34: vpiReturnEvent with no delay (vpiNoDelay) schedules nothing, so the
// return value is NULL.
TEST_F(VpiPutValueSim, ReturnEventWithoutDelayReturnsNull) {
  auto* var = sim_ctx_.CreateVariable("rn", 32);
  var->value = MakeLogic4VecVal(arena_, 32, 0);
  vpi_ctx_.Attach(sim_ctx_);

  vpiHandle h = vpi_handle_by_name("rn", nullptr);
  s_vpi_value val = {};
  val.format = vpiIntVal;
  val.value.integer = 3;
  vpiHandle ev = vpi_put_value(h, &val, nullptr, vpiNoDelay | vpiReturnEvent);
  EXPECT_EQ(ev, nullptr);
}

// §38.34: even when a delay schedules an event, the return value is NULL unless
// the vpiReturnEvent bit mask was requested. Here a delayed put without the
// mask returns NULL.
TEST_F(VpiPutValueSim, DelayWithoutReturnEventReturnsNull) {
  auto* var = sim_ctx_.CreateVariable("dn", 32);
  var->value = MakeLogic4VecVal(arena_, 32, 0);
  vpi_ctx_.Attach(sim_ctx_);

  vpiHandle h = vpi_handle_by_name("dn", nullptr);
  s_vpi_value val = {};
  val.format = vpiIntVal;
  val.value.integer = 6;
  s_vpi_time time = {};
  time.type = vpiSimTime;
  time.low = 4;
  vpiHandle ev = vpi_put_value(h, &val, &time, vpiTransportDelay);
  EXPECT_EQ(ev, nullptr);
}

// §38.34: a scheduled event is cancelled by calling the routine with the
// vpiSchedEvent handle and vpiCancelEvent; afterwards vpi_get(vpiScheduled)
// reports it is no longer in the queue. value_p and time_p are not needed.
TEST_F(VpiPutValueSim, CancelEventClearsScheduled) {
  auto* var = sim_ctx_.CreateVariable("ce", 32);
  var->value = MakeLogic4VecVal(arena_, 32, 0);
  vpi_ctx_.Attach(sim_ctx_);

  vpiHandle h = vpi_handle_by_name("ce", nullptr);
  s_vpi_value val = {};
  val.format = vpiIntVal;
  val.value.integer = 1;
  s_vpi_time time = {};
  time.type = vpiSimTime;
  time.low = 7;
  vpiHandle ev =
      vpi_put_value(h, &val, &time, vpiTransportDelay | vpiReturnEvent);
  ASSERT_NE(ev, nullptr);
  ASSERT_EQ(vpi_get(vpiScheduled, ev), 1);

  vpiHandle ret = vpi_put_value(ev, nullptr, nullptr, vpiCancelEvent);
  EXPECT_EQ(ret, nullptr);
  EXPECT_EQ(vpi_get(vpiScheduled, ev), 0);
}

// §38.34: it shall not be an error to cancel an event that has already occurred
// - cancelling a handle that is no longer scheduled simply does nothing.
TEST_F(VpiPutValueSim, CancelAlreadyOccurredIsNotError) {
  auto* var = sim_ctx_.CreateVariable("co", 32);
  var->value = MakeLogic4VecVal(arena_, 32, 0);
  vpi_ctx_.Attach(sim_ctx_);

  vpiHandle h = vpi_handle_by_name("co", nullptr);
  s_vpi_value val = {};
  val.format = vpiIntVal;
  val.value.integer = 1;
  s_vpi_time time = {};
  time.type = vpiSimTime;
  time.low = 2;
  vpiHandle ev =
      vpi_put_value(h, &val, &time, vpiInertialDelay | vpiReturnEvent);
  ASSERT_NE(ev, nullptr);

  // Cancel once (the event leaves the queue), then cancel again: still no
  // error.
  vpi_put_value(ev, nullptr, nullptr, vpiCancelEvent);
  SVpiErrorInfo info = {};
  vpi_put_value(ev, nullptr, nullptr, vpiCancelEvent);
  EXPECT_EQ(vpi_chk_error(&info), 0);
  EXPECT_EQ(vpi_get(vpiScheduled, ev), 0);
}

// §38.34: vpiForceFlag forces the passed value onto the object - the same
// operation as a procedural force (10.6.2) - so the object holds the value and
// is marked forced.
TEST_F(VpiPutValueSim, ForceFlagForcesValue) {
  auto* var = sim_ctx_.CreateVariable("ff", 32);
  var->value = MakeLogic4VecVal(arena_, 32, 0);
  vpi_ctx_.Attach(sim_ctx_);

  vpiHandle h = vpi_handle_by_name("ff", nullptr);
  s_vpi_value val = {};
  val.format = vpiIntVal;
  val.value.integer = 42;
  vpi_put_value(h, &val, nullptr, vpiForceFlag);

  EXPECT_TRUE(var->is_forced);
  EXPECT_EQ(var->value.ToUint64(), 42u);
  EXPECT_EQ(var->forced_value.ToUint64(), 42u);
}

// §38.34: vpiReleaseFlag releases a forced value (the procedural release of
// 10.6.2) and updates value_p with the object's value after the release.
TEST_F(VpiPutValueSim, ReleaseFlagReleasesAndUpdatesValue) {
  auto* var = sim_ctx_.CreateVariable("rl", 32);
  var->value = MakeLogic4VecVal(arena_, 32, 0);
  vpi_ctx_.Attach(sim_ctx_);

  vpiHandle h = vpi_handle_by_name("rl", nullptr);
  s_vpi_value forced = {};
  forced.format = vpiIntVal;
  forced.value.integer = 9;
  vpi_put_value(h, &forced, nullptr, vpiForceFlag);
  ASSERT_TRUE(var->is_forced);

  s_vpi_value out = {};
  out.format = vpiIntVal;
  vpi_put_value(h, &out, nullptr, vpiReleaseFlag);

  EXPECT_FALSE(var->is_forced);
  EXPECT_EQ(out.value.integer, 9);
}

// §38.34: putting to a vpiNamedEvent object toggles (triggers) the named event,
// and value_p may be NULL because the event needs no value.
TEST_F(VpiPutValueSim, NamedEventToggleAcceptsNullValue) {
  auto* var = sim_ctx_.CreateVariable("ne", 1);
  var->value = MakeLogic4VecVal(arena_, 1, 0);
  var->is_event = true;
  vpi_ctx_.Attach(sim_ctx_);
  vpi_ctx_.SetScheduler(&scheduler_);

  vpiHandle h = vpi_handle_by_name("ne", nullptr);
  ASSERT_NE(h, nullptr);

  vpiHandle ret = vpi_put_value(h, nullptr, nullptr, vpiNoDelay);
  EXPECT_EQ(ret, nullptr);
  EXPECT_EQ(var->triggered_ticks, scheduler_.CurrentTime().ticks);
}

// §38.34: it is illegal to put a value in vpiStringVal format to a real object;
// the put is rejected and recorded as an error.
TEST_F(VpiPutValueSim, StringFormatToRealIsIllegal) {
  auto* var = sim_ctx_.CreateVariable("sr", 64);
  var->value = MakeLogic4VecVal(arena_, 64, 0);
  var->value.is_real = true;
  vpi_ctx_.Attach(sim_ctx_);

  vpiHandle h = vpi_handle_by_name("sr", nullptr);
  s_vpi_value val = {};
  val.format = vpiStringVal;
  val.value.str = "hi";
  vpi_put_value(h, &val, nullptr, vpiNoDelay);

  SVpiErrorInfo info = {};
  EXPECT_EQ(vpi_chk_error(&info), vpiError);
}

// §38.34: it is illegal to put a value in vpiStrengthVal format to a vector
// object (one wider than a single bit).
TEST_F(VpiPutValueSim, StrengthFormatToVectorIsIllegal) {
  auto* var = sim_ctx_.CreateVariable("sv", 32);
  var->value = MakeLogic4VecVal(arena_, 32, 0);
  vpi_ctx_.Attach(sim_ctx_);

  vpiHandle h = vpi_handle_by_name("sv", nullptr);
  s_vpi_value val = {};
  val.format = vpiStrengthVal;
  vpi_put_value(h, &val, nullptr, vpiNoDelay);

  SVpiErrorInfo info = {};
  EXPECT_EQ(vpi_chk_error(&info), vpiError);
}

// §38.34 (edge): the vpiStrengthVal restriction is scoped to vector objects, so
// supplying that format for a one-bit object is not flagged as an error.
TEST_F(VpiPutValueSim, StrengthFormatToScalarIsNotIllegal) {
  auto* var = sim_ctx_.CreateVariable("ss", 1);
  var->value = MakeLogic4VecVal(arena_, 1, 0);
  vpi_ctx_.Attach(sim_ctx_);

  vpiHandle h = vpi_handle_by_name("ss", nullptr);
  s_vpi_value val = {};
  val.format = vpiStrengthVal;
  vpi_put_value(h, &val, nullptr, vpiNoDelay);

  SVpiErrorInfo info = {};
  EXPECT_EQ(vpi_chk_error(&info), 0);
}

// §38.34 (edge): the vpiStringVal restriction is scoped to real objects, so
// supplying that format for an ordinary (non-real) object is not flagged.
TEST_F(VpiPutValueSim, StringFormatToNonRealIsNotIllegal) {
  auto* var = sim_ctx_.CreateVariable("sn", 32);
  var->value = MakeLogic4VecVal(arena_, 32, 0);
  vpi_ctx_.Attach(sim_ctx_);

  vpiHandle h = vpi_handle_by_name("sn", nullptr);
  s_vpi_value val = {};
  val.format = vpiStringVal;
  val.value.str = "hi";
  vpi_put_value(h, &val, nullptr, vpiNoDelay);

  SVpiErrorInfo info = {};
  EXPECT_EQ(vpi_chk_error(&info), 0);
}

// §38.34 (edge): vpiCancelEvent acts only on a vpiSchedEvent handle. Asking to
// cancel through an ordinary object handle leaves it alone and raises no error.
TEST_F(VpiPutValueSim, CancelOnNonSchedEventHandleIsNoError) {
  auto* var = sim_ctx_.CreateVariable("cn", 32);
  var->value = MakeLogic4VecVal(arena_, 32, 7);
  vpi_ctx_.Attach(sim_ctx_);

  vpiHandle h = vpi_handle_by_name("cn", nullptr);
  ASSERT_NE(h, nullptr);

  vpiHandle ret = vpi_put_value(h, nullptr, nullptr, vpiCancelEvent);
  EXPECT_EQ(ret, nullptr);

  SVpiErrorInfo info = {};
  EXPECT_EQ(vpi_chk_error(&info), 0);
  EXPECT_EQ(var->value.ToUint64(), 7u);
}

// §38.34: a put to a sequential UDP with a scheduled delay mode (here
// vpiTransportDelay) is an error - such an object accepts only vpiNoDelay.
TEST_F(VpiPutValueSim, SequentialUdpRejectsDelayMode) {
  auto* var = sim_ctx_.CreateVariable("up", 1);
  var->value = MakeLogic4VecVal(arena_, 1, 0);
  vpi_ctx_.Attach(sim_ctx_);

  vpiHandle h = vpi_handle_by_name("up", nullptr);
  ASSERT_NE(h, nullptr);
  h->type = vpiSeqPrim;

  s_vpi_value val = {};
  val.format = vpiScalarVal;
  val.value.scalar = vpi1;
  s_vpi_time time = {};
  time.type = vpiSimTime;
  time.low = 3;
  vpi_put_value(h, &val, &time, vpiTransportDelay);

  SVpiErrorInfo info = {};
  EXPECT_EQ(vpi_chk_error(&info), vpiError);
  // The rejected put left the object unchanged.
  EXPECT_EQ(var->value.words[0].aval & 1, 0u);
}

// §38.34: the same sequential UDP accepts a value when the required vpiNoDelay
// flag is used, applying it with no error.
TEST_F(VpiPutValueSim, SequentialUdpAcceptsNoDelay) {
  auto* var = sim_ctx_.CreateVariable("ua", 1);
  var->value = MakeLogic4VecVal(arena_, 1, 0);
  vpi_ctx_.Attach(sim_ctx_);

  vpiHandle h = vpi_handle_by_name("ua", nullptr);
  ASSERT_NE(h, nullptr);
  h->type = vpiSeqPrim;

  s_vpi_value val = {};
  val.format = vpiScalarVal;
  val.value.scalar = vpi1;
  vpi_put_value(h, &val, nullptr, vpiNoDelay);

  SVpiErrorInfo info = {};
  EXPECT_EQ(vpi_chk_error(&info), 0);
  EXPECT_EQ(var->value.words[0].aval & 1, 1u);
}

}  // namespace
}  // namespace delta
