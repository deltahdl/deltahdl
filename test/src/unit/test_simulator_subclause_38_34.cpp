#include <gtest/gtest.h>

#include <cstdint>
#include <cstring>
#include <functional>

#include "common/arena.h"
#include "common/diagnostic.h"
#include "common/source_mgr.h"
#include "common/types.h"
#include "fixture_vpi_run.h"
#include "simulator/net.h"
#include "simulator/sim_context.h"
#include "simulator/sv_vpi_user.h"
#include "simulator/vpi_context.h"
#include "simulator/vpi_globals.h"
#include "simulator/vpi_internal.h"
#include "simulator/vpi_object.h"
#include "simulator/vpi_user.h"

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

  vpiHandle h = vpi_handle_by_name(VpiText("d"), nullptr);
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

  vpiHandle h = vpi_handle_by_name(VpiText("di"), nullptr);
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

  vpiHandle h = vpi_handle_by_name(VpiText("rf"), nullptr);
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

  vpiHandle h = vpi_handle_by_name(VpiText("sf"), nullptr);
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

  vpiHandle h = vpi_handle_by_name(VpiText("re"), nullptr);
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

  vpiHandle h = vpi_handle_by_name(VpiText("rn"), nullptr);
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

  vpiHandle h = vpi_handle_by_name(VpiText("dn"), nullptr);
  s_vpi_value val = {};
  val.format = vpiIntVal;
  val.value.integer = 6;
  s_vpi_time time = {};
  time.type = vpiSimTime;
  time.low = 4;
  vpiHandle ev = vpi_put_value(h, &val, &time, vpiTransportDelay);
  EXPECT_EQ(ev, nullptr);
}

// §38.34 (input form): vpiPureTransportDelay is a named delay mode of its own
// (transport delay that removes no events); a put using it applies the value to
// an ordinary object just like the other scheduled delay modes.
TEST_F(VpiPutValueSim, PutValuePureTransportDelay) {
  auto* var = sim_ctx_.CreateVariable("dp", 32);
  var->value = MakeLogic4VecVal(arena_, 32, 0);
  vpi_ctx_.Attach(sim_ctx_);

  vpiHandle h = vpi_handle_by_name(VpiText("dp"), nullptr);
  s_vpi_value val = {};
  val.format = vpiIntVal;
  val.value.integer = 55;
  s_vpi_time time = {};
  time.type = vpiSimTime;
  time.low = 12;
  vpi_put_value(h, &val, &time, vpiPureTransportDelay);

  EXPECT_EQ(var->value.ToUint64(), 55u);
}

// §38.34 (input form): vpiTransportDelay is the third named scheduled delay
// mode (modified transport delay); like the other scheduled modes it applies
// the passed value to an ordinary object. The companion
// DelayWithoutReturnEventReturnsNull already checks its NULL return; this
// checks the value is actually written.
TEST_F(VpiPutValueSim, PutValueTransportDelay) {
  auto* var = sim_ctx_.CreateVariable("dt", 32);
  var->value = MakeLogic4VecVal(arena_, 32, 0);
  vpi_ctx_.Attach(sim_ctx_);

  vpiHandle h = vpi_handle_by_name(VpiText("dt"), nullptr);
  s_vpi_value val = {};
  val.format = vpiIntVal;
  val.value.integer = 99;
  s_vpi_time time = {};
  time.type = vpiSimTime;
  time.low = 8;
  vpi_put_value(h, &val, &time, vpiTransportDelay);

  EXPECT_EQ(var->value.ToUint64(), 99u);
}

// §38.34: putting a value to a vpiNet with one of the delay modes overrides the
// net's resolved value. The override holds until a driver changes value, at
// which point the net is reevaluated by the normal resolution algorithm. Here
// the put overrides the resolved value, then a fresh driver plus a resolution
// pass replaces it - the override is no longer in effect.
TEST_F(VpiPutValueSim, NetPutOverridesResolvedValueUntilDriverChanges) {
  Net* net = sim_ctx_.CreateNet("nw", NetType::kWire, 32);
  ASSERT_NE(net, nullptr);
  ASSERT_NE(net->resolved, nullptr);

  VpiHandle h = vpi_ctx_.CreateNetObj("nw", net, 32);
  ASSERT_NE(h, nullptr);

  s_vpi_value val = {};
  val.format = vpiIntVal;
  val.value.integer = 123;
  vpi_put_value(VpiHandleOf(h), &val, nullptr, vpiNoDelay);
  // The supplied value overrides the resolved value of the net.
  EXPECT_EQ(net->resolved->value.ToUint64(), 123u);

  // A driver changes value and the net is reevaluated: normal resolution wins
  // and the override no longer stands.
  net->drivers.push_back(MakeLogic4VecVal(arena_, 32, 5));
  net->Resolve(arena_);
  EXPECT_EQ(net->resolved->value.ToUint64(), 5u);
}

// §38.34: a scheduled event is cancelled by calling the routine with the
// vpiSchedEvent handle and vpiCancelEvent; afterwards vpi_get(vpiScheduled)
// reports it is no longer in the queue. value_p and time_p are not needed.
TEST_F(VpiPutValueSim, CancelEventClearsScheduled) {
  auto* var = sim_ctx_.CreateVariable("ce", 32);
  var->value = MakeLogic4VecVal(arena_, 32, 0);
  vpi_ctx_.Attach(sim_ctx_);

  vpiHandle h = vpi_handle_by_name(VpiText("ce"), nullptr);
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

  vpiHandle h = vpi_handle_by_name(VpiText("co"), nullptr);
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
  s_vpi_error_info info = {};
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

  vpiHandle h = vpi_handle_by_name(VpiText("ff"), nullptr);
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

  vpiHandle h = vpi_handle_by_name(VpiText("rl"), nullptr);
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

  vpiHandle h = vpi_handle_by_name(VpiText("ne"), nullptr);
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

  vpiHandle h = vpi_handle_by_name(VpiText("sr"), nullptr);
  s_vpi_value val = {};
  val.format = vpiStringVal;
  val.value.str = VpiText("hi");
  vpi_put_value(h, &val, nullptr, vpiNoDelay);

  s_vpi_error_info info = {};
  EXPECT_EQ(vpi_chk_error(&info), vpiError);
}

// §38.34: it is illegal to put a value in vpiStrengthVal format to a vector
// object (one wider than a single bit).
TEST_F(VpiPutValueSim, StrengthFormatToVectorIsIllegal) {
  auto* var = sim_ctx_.CreateVariable("sv", 32);
  var->value = MakeLogic4VecVal(arena_, 32, 0);
  vpi_ctx_.Attach(sim_ctx_);

  vpiHandle h = vpi_handle_by_name(VpiText("sv"), nullptr);
  s_vpi_value val = {};
  val.format = vpiStrengthVal;
  vpi_put_value(h, &val, nullptr, vpiNoDelay);

  s_vpi_error_info info = {};
  EXPECT_EQ(vpi_chk_error(&info), vpiError);
}

// §38.34 (edge): the vpiStrengthVal restriction is scoped to vector objects, so
// supplying that format for a one-bit object is not flagged as an error.
TEST_F(VpiPutValueSim, StrengthFormatToScalarIsNotIllegal) {
  auto* var = sim_ctx_.CreateVariable("ss", 1);
  var->value = MakeLogic4VecVal(arena_, 1, 0);
  vpi_ctx_.Attach(sim_ctx_);

  vpiHandle h = vpi_handle_by_name(VpiText("ss"), nullptr);
  s_vpi_value val = {};
  val.format = vpiStrengthVal;
  vpi_put_value(h, &val, nullptr, vpiNoDelay);

  s_vpi_error_info info = {};
  EXPECT_EQ(vpi_chk_error(&info), 0);
}

// §38.34 (edge): the vpiStringVal restriction is scoped to real objects, so
// supplying that format for an ordinary (non-real) object is not flagged.
TEST_F(VpiPutValueSim, StringFormatToNonRealIsNotIllegal) {
  auto* var = sim_ctx_.CreateVariable("sn", 32);
  var->value = MakeLogic4VecVal(arena_, 32, 0);
  vpi_ctx_.Attach(sim_ctx_);

  vpiHandle h = vpi_handle_by_name(VpiText("sn"), nullptr);
  s_vpi_value val = {};
  val.format = vpiStringVal;
  val.value.str = VpiText("hi");
  vpi_put_value(h, &val, nullptr, vpiNoDelay);

  s_vpi_error_info info = {};
  EXPECT_EQ(vpi_chk_error(&info), 0);
}

// §38.34 (edge): vpiCancelEvent acts only on a vpiSchedEvent handle. Asking to
// cancel through an ordinary object handle leaves it alone and raises no error.
TEST_F(VpiPutValueSim, CancelOnNonSchedEventHandleIsNoError) {
  auto* var = sim_ctx_.CreateVariable("cn", 32);
  var->value = MakeLogic4VecVal(arena_, 32, 7);
  vpi_ctx_.Attach(sim_ctx_);

  vpiHandle h = vpi_handle_by_name(VpiText("cn"), nullptr);
  ASSERT_NE(h, nullptr);

  vpiHandle ret = vpi_put_value(h, nullptr, nullptr, vpiCancelEvent);
  EXPECT_EQ(ret, nullptr);

  s_vpi_error_info info = {};
  EXPECT_EQ(vpi_chk_error(&info), 0);
  EXPECT_EQ(var->value.ToUint64(), 7u);
}

// §38.34: a put to a sequential UDP with a scheduled delay mode (here
// vpiTransportDelay) is an error - such an object accepts only vpiNoDelay.
TEST_F(VpiPutValueSim, SequentialUdpRejectsDelayMode) {
  auto* var = sim_ctx_.CreateVariable("up", 1);
  var->value = MakeLogic4VecVal(arena_, 1, 0);
  vpi_ctx_.Attach(sim_ctx_);

  vpiHandle h = vpi_handle_by_name(VpiText("up"), nullptr);
  ASSERT_NE(h, nullptr);
  VpiObjectOf(h)->type = vpiSeqPrim;

  s_vpi_value val = {};
  val.format = vpiScalarVal;
  val.value.scalar = vpi1;
  s_vpi_time time = {};
  time.type = vpiSimTime;
  time.low = 3;
  vpi_put_value(h, &val, &time, vpiTransportDelay);

  s_vpi_error_info info = {};
  EXPECT_EQ(vpi_chk_error(&info), vpiError);
  // The rejected put left the object unchanged.
  EXPECT_EQ(var->value.words[0].aval & 1, 0u);
}

// §38.34 (input form): the sequential-UDP delay restriction covers every
// scheduled delay mode, not just vpiTransportDelay. Putting with
// vpiPureTransportDelay - another of the delay modes the clause names - is
// likewise an error, and the UDP is left unchanged.
TEST_F(VpiPutValueSim, SequentialUdpRejectsPureTransportDelay) {
  auto* var = sim_ctx_.CreateVariable("uq", 1);
  var->value = MakeLogic4VecVal(arena_, 1, 0);
  vpi_ctx_.Attach(sim_ctx_);

  vpiHandle h = vpi_handle_by_name(VpiText("uq"), nullptr);
  ASSERT_NE(h, nullptr);
  VpiObjectOf(h)->type = vpiSeqPrim;

  s_vpi_value val = {};
  val.format = vpiScalarVal;
  val.value.scalar = vpi1;
  s_vpi_time time = {};
  time.type = vpiSimTime;
  time.low = 3;
  vpi_put_value(h, &val, &time, vpiPureTransportDelay);

  s_vpi_error_info info = {};
  EXPECT_EQ(vpi_chk_error(&info), vpiError);
  EXPECT_EQ(var->value.words[0].aval & 1, 0u);
}

// §38.34 (input form): the sequential-UDP restriction rejects vpiInertialDelay
// as well - it is the last of the three scheduled delay modes, and none of them
// is allowed on a sequential UDP, which accepts only vpiNoDelay. The put is an
// error and the object is left unchanged.
TEST_F(VpiPutValueSim, SequentialUdpRejectsInertialDelay) {
  auto* var = sim_ctx_.CreateVariable("ui", 1);
  var->value = MakeLogic4VecVal(arena_, 1, 0);
  vpi_ctx_.Attach(sim_ctx_);

  vpiHandle h = vpi_handle_by_name(VpiText("ui"), nullptr);
  ASSERT_NE(h, nullptr);
  VpiObjectOf(h)->type = vpiSeqPrim;

  s_vpi_value val = {};
  val.format = vpiScalarVal;
  val.value.scalar = vpi1;
  s_vpi_time time = {};
  time.type = vpiSimTime;
  time.low = 3;
  vpi_put_value(h, &val, &time, vpiInertialDelay);

  s_vpi_error_info info = {};
  EXPECT_EQ(vpi_chk_error(&info), vpiError);
  EXPECT_EQ(var->value.words[0].aval & 1, 0u);
}

// §38.34: the same sequential UDP accepts a value when the required vpiNoDelay
// flag is used, applying it with no error.
TEST_F(VpiPutValueSim, SequentialUdpAcceptsNoDelay) {
  auto* var = sim_ctx_.CreateVariable("ua", 1);
  var->value = MakeLogic4VecVal(arena_, 1, 0);
  vpi_ctx_.Attach(sim_ctx_);

  vpiHandle h = vpi_handle_by_name(VpiText("ua"), nullptr);
  ASSERT_NE(h, nullptr);
  VpiObjectOf(h)->type = vpiSeqPrim;

  s_vpi_value val = {};
  val.format = vpiScalarVal;
  val.value.scalar = vpi1;
  vpi_put_value(h, &val, nullptr, vpiNoDelay);

  s_vpi_error_info info = {};
  EXPECT_EQ(vpi_chk_error(&info), 0);
  EXPECT_EQ(var->value.words[0].aval & 1, 1u);
}

// §38.34 with Table 38-3: a value in any format the table lists is decoded
// into every word of the object it is put to (#5101).
class VpiPutValueFormats : public VpiPutValueSim {
 protected:
  // The variable `name`, `width` bits wide and 0, after `value` is put to it.
  const Logic4Vec& PutTo(const char* name, uint32_t width, s_vpi_value value) {
    auto* var = sim_ctx_.CreateVariable(name, width);
    var->value = MakeLogic4VecVal(arena_, width, 0);
    vpi_ctx_.Attach(sim_ctx_);
    vpi_put_value(vpi_handle_by_name(VpiText(name), nullptr), &value, nullptr,
                  vpiNoDelay);
    return var->value;
  }
};

TEST_F(VpiPutValueFormats, ABinaryStringSetsEachBitXAndZIncluded) {
  s_vpi_value val = {};
  val.format = vpiBinStrVal;
  val.value.str = VpiText("1x0z");
  const Logic4Vec& v = PutTo("bs", 4, val);
  EXPECT_EQ(v.words[0].aval, 0b1100u);
  EXPECT_EQ(v.words[0].bval, 0b0101u);
}

TEST_F(VpiPutValueFormats, AnOctalStringSetsThreeBitsPerDigit) {
  s_vpi_value val = {};
  val.format = vpiOctStrVal;
  val.value.str = VpiText("751");
  EXPECT_EQ(PutTo("os", 9, val).ToUint64(), 0751u);
}

TEST_F(VpiPutValueFormats, AHexStringSetsFourBitsPerDigit) {
  s_vpi_value val = {};
  val.format = vpiHexStrVal;
  val.value.str = VpiText("DeadBeef");
  EXPECT_EQ(PutTo("hs", 32, val).ToUint64(), 0xDEADBEEFu);
}

TEST_F(VpiPutValueFormats, ANegativeDecimalStringIsTwosComplement) {
  s_vpi_value val = {};
  val.format = vpiDecStrVal;
  val.value.str = VpiText("-5");
  EXPECT_EQ(PutTo("dn", 8, val).ToUint64(), 0xFBu);
}

TEST_F(VpiPutValueFormats, ADecimalStringReachesPastTheFirstWord) {
  s_vpi_value val = {};
  val.format = vpiDecStrVal;
  val.value.str = VpiText("18446744073709551621");  // 2^64 + 5
  const Logic4Vec& v = PutTo("dw", 72, val);
  ASSERT_EQ(v.nwords, 2u);
  EXPECT_EQ(v.words[0].aval, 5u);
  EXPECT_EQ(v.words[1].aval, 1u);
}

TEST_F(VpiPutValueFormats, AStringSetsEightBitsPerCharacter) {
  s_vpi_value val = {};
  val.format = vpiStringVal;
  val.value.str = VpiText("AB");
  EXPECT_EQ(PutTo("ss", 16, val).ToUint64(), 0x4142u);
}

TEST_F(VpiPutValueFormats, ATimeSetsTheHighAndLowWords) {
  s_vpi_time time = {};
  time.type = vpiSimTime;
  time.high = 3;
  time.low = 7;
  s_vpi_value val = {};
  val.format = vpiTimeVal;
  val.value.time = &time;
  EXPECT_EQ(PutTo("ts", 64, val).ToUint64(), (uint64_t{3} << 32) | 7);
}

TEST_F(VpiPutValueFormats, AVectorSetsEveryWordItsArrayHolds) {
  s_vpi_vecval vec[3] = {{1, 0}, {2, 0}, {3, 4}};
  s_vpi_value val = {};
  val.format = vpiVectorVal;
  val.value.vector = vec;
  const Logic4Vec& v = PutTo("vs", 96, val);
  ASSERT_EQ(v.nwords, 2u);
  EXPECT_EQ(v.words[0].aval, (uint64_t{2} << 32) | 1);
  EXPECT_EQ(v.words[0].bval, 0u);
  EXPECT_EQ(v.words[1].aval, 3u);
  EXPECT_EQ(v.words[1].bval, 4u);
}

TEST_F(VpiPutValueFormats, ANegativeIntegerFillsAWideObject) {
  s_vpi_value val = {};
  val.format = vpiIntVal;
  val.value.integer = -1;
  const Logic4Vec& v = PutTo("in", 96, val);
  ASSERT_EQ(v.nwords, 2u);
  EXPECT_EQ(v.words[0].aval, ~uint64_t{0});
  EXPECT_EQ(v.words[1].aval, 0xFFFFFFFFu);
}

// What `$put` does each time the design calls it.
std::function<void()>& Putter() {
  static std::function<void()> putter;
  return putter;
}

// A run whose design calls `$put`, which makes the case's puts.
class PutsOfARun : public VpiDesignRun {
 protected:
  void SetUp() override {
    VpiDesignRun::SetUp();
    s_vpi_systf_data data = {};
    data.type = vpiSysTask;
    data.tfname = VpiText("$put");
    data.calltf = [](PLI_BYTE8*) -> PLI_INT32 {
      Putter()();
      return 0;
    };
    ASSERT_NE(vpi_register_systf(&data), nullptr);
  }

  // The integer value `name` holds once the run is over.
  static int IntOf(const char* name) {
    s_vpi_value value = {};
    value.format = vpiIntVal;
    vpi_get_value(By(name), &value);
    return value.value.integer;
  }
};

// Puts `value` into the object `name` names with `flags`, after `delay` for
// a delay mode; answers the event handle the put returns.
vpiHandle PutInt(const char* name, int value, int flags, uint32_t delay = 0) {
  s_vpi_value val = {};
  val.format = vpiIntVal;
  val.value.integer = value;
  s_vpi_time time = {};
  time.type = vpiSimTime;
  time.low = delay;
  return vpi_put_value(vpi_handle_by_name(VpiText(name), nullptr), &val, &time,
                       flags);
}

// §38.34 with §9.4.2: a value put with vpiNoDelay is an update of the object,
// which resumes an event control waiting on it (#5112).
TEST_F(PutsOfARun, APutWakesAnEventControlOnItsObject) {
  Putter() = [] { PutInt("top.v", 5, vpiNoDelay); };
  Run("module top; int v, seen;\n"
      "  always @(v) seen = v;\n"
      "  initial #1 $put;\n"
      "endmodule\n");
  EXPECT_EQ(IntOf("top.seen"), 5);
}

// §38.34 with §37.33 and §9.4.3: a value put into a class object's property
// resumes a class task waiting on a condition over it (#5113).
TEST_F(PutsOfARun, APutIntoAClassPropertyWakesATaskWaitingOnIt) {
  Putter() = [] {
    vpiHandle obj =
        vpi_handle(vpiClassObj, vpi_handle_by_name(VpiText("top.c"), nullptr));
    vpiHandle it = vpi_iterate(vpiVariables, obj);
    for (vpiHandle v = it != nullptr ? vpi_scan(it) : nullptr; v != nullptr;
         v = vpi_scan(it)) {
      if (std::strcmp(vpi_get_str(vpiName, v), "val") != 0) continue;
      s_vpi_value val = {};
      val.format = vpiIntVal;
      val.value.integer = 9;
      vpi_put_value(v, &val, nullptr, vpiNoDelay);
    }
  };
  Run("module top; int saw = 0;\n"
      "  class C; int val;\n"
      "    task wait_for_nine(); wait (val == 9); saw = 1; endtask\n"
      "  endclass\n"
      "  C c = new;\n"
      "  initial begin fork c.wait_for_nine(); join_none #4 $put; #1; end\n"
      "endmodule\n");
  EXPECT_EQ(IntOf("top.saw"), 1);
}

constexpr const char* kDelayedPut =
    "module top; timeunit 1ns; timeprecision 1ns; int v, v_at3, v_at5;\n"
    "  initial begin #1 $put; #2 v_at3 = v; #2 v_at5 = v; end\n"
    "endmodule\n";

// §38.34: a put with vpiInertialDelay sets the object once its delay has
// passed, not at once: 6 put at time 1 with a delay of 3 is 0 at time 3 and
// 6 at time 5 (#5114).
TEST_F(PutsOfARun, AnInertialPutTakesEffectAfterItsDelay) {
  Putter() = [] { PutInt("top.v", 6, vpiInertialDelay, 3); };
  Run(kDelayedPut);
  EXPECT_EQ(IntOf("top.v_at3"), 0);
  EXPECT_EQ(IntOf("top.v_at5"), 6);
}

// §38.34: an event a delayed put scheduled and vpiCancelEvent then cancelled
// is taken out of the event queue and never takes place (#5115).
TEST_F(PutsOfARun, ACancelledPutNeverTakesEffect) {
  Putter() = [] {
    vpiHandle event = PutInt("top.v", 7, vpiTransportDelay | vpiReturnEvent, 2);
    vpi_put_value(event, nullptr, nullptr, vpiCancelEvent);
  };
  Run(kDelayedPut);
  EXPECT_EQ(IntOf("top.v_at5"), 0);
}

int& ReleasedValue() {
  static int released = -1;
  return released;
}

// §38.34 with §10.6.2: vpiReleaseFlag releases a net vpiForceFlag forced, the
// net taking at once the value its driver gives, which value_p reports
// (#5116).
TEST_F(PutsOfARun, AReleasedNetTakesItsDriversValue) {
  ReleasedValue() = -1;
  Putter() = [] {
    static int calls = 0;
    if (calls++ % 2 == 0) {
      PutInt("top.w", 0, vpiForceFlag);
      return;
    }
    s_vpi_value val = {};
    val.format = vpiIntVal;
    vpi_put_value(vpi_handle_by_name(VpiText("top.w"), nullptr), &val, nullptr,
                  vpiReleaseFlag);
    ReleasedValue() = val.value.integer;
  };
  Run("module top; logic d = 1; wire w = d; logic w_at2;\n"
      "  initial begin #1 $put; #1 w_at2 = w; #1 $put; #1; end\n"
      "endmodule\n");
  EXPECT_EQ(IntOf("top.w_at2"), 0);
  EXPECT_EQ(ReleasedValue(), 1);
  EXPECT_EQ(IntOf("top.w"), 1);
}

// §38.34: with a null handle there is nothing to write, and a put of no
// value to a variable, which needs one, writes nothing; neither hands back a
// handle.
TEST_F(VpiPutValueSim, ANullHandleOrValueWritesNothing) {
  auto* var = sim_ctx_.CreateVariable("nh", 8);
  var->value = MakeLogic4VecVal(arena_, 8, 3);
  vpi_ctx_.Attach(sim_ctx_);
  vpiHandle h = vpi_handle_by_name(VpiText("nh"), nullptr);
  ASSERT_NE(h, nullptr);

  s_vpi_value val = {};
  val.format = vpiIntVal;
  val.value.integer = 9;
  EXPECT_EQ(vpi_put_value(nullptr, &val, nullptr, vpiNoDelay), nullptr);
  EXPECT_EQ(vpi_put_value(h, nullptr, nullptr, vpiNoDelay), nullptr);
  EXPECT_EQ(var->value.ToUint64(), 3u);
}

// §38.34: outside a run, with no scheduler to note it in, a put to a net
// with no storage of its own and a put triggering a named event write
// nothing and stamp no trigger time.
TEST_F(VpiPutValueSim, APutWithNoSchedulerNotesNothing) {
  Net bare;
  vpiHandle net = VpiHandleOf(vpi_ctx_.CreateNetObj("bare", &bare, 8));
  auto* event = sim_ctx_.CreateVariable("ev", 1);
  event->is_event = true;
  vpi_ctx_.Attach(sim_ctx_);
  vpiHandle ev = vpi_handle_by_name(VpiText("ev"), nullptr);
  ASSERT_NE(ev, nullptr);

  s_vpi_value val = {};
  val.format = vpiIntVal;
  val.value.integer = 1;
  EXPECT_EQ(vpi_put_value(net, &val, nullptr, vpiNoDelay), nullptr);
  EXPECT_EQ(vpi_put_value(ev, nullptr, nullptr, vpiNoDelay), nullptr);
  EXPECT_EQ(event->triggered_ticks, UINT64_MAX);
}

// §38.34: a delay mode takes its delay from time_p, a delay being present
// when the time is nonzero in its high word, its low word or its real value,
// and absent when no time is given, the write then made at once. A present
// delay with vpiReturnEvent hands back the scheduled event's handle.
TEST_F(VpiPutValueSim, ADelayIsPresentWhereAnyPartOfTheTimeIsNonzero) {
  auto* var = sim_ctx_.CreateVariable("dl", 8);
  var->value = MakeLogic4VecVal(arena_, 8, 0);
  vpi_ctx_.Attach(sim_ctx_);
  vpiHandle h = vpi_handle_by_name(VpiText("dl"), nullptr);
  ASSERT_NE(h, nullptr);
  s_vpi_value val = {};
  val.format = vpiIntVal;
  val.value.integer = 4;
  const int kFlags = vpiInertialDelay | vpiReturnEvent;

  EXPECT_EQ(vpi_put_value(h, &val, nullptr, kFlags), nullptr);
  EXPECT_EQ(var->value.ToUint64(), 4u);
  s_vpi_time high = {};
  high.type = vpiSimTime;
  high.high = 1;
  EXPECT_NE(vpi_put_value(h, &val, &high, kFlags), nullptr);
  s_vpi_time real = {};
  real.type = vpiScaledRealTime;
  real.real = 2.0;
  EXPECT_NE(vpi_put_value(h, &val, &real, kFlags), nullptr);
}

// §38.36.2 with §4.4.2.9: a cbReadOnlySynch routine writes no value, but a
// cancel writes none, so a cancel made then is no error.
TEST_F(VpiPutValueSim, ACancelFromAReadOnlySynchCallbackIsNoError) {
  auto* var = sim_ctx_.CreateVariable("cn", 8);
  var->value = MakeLogic4VecVal(arena_, 8, 1);
  vpi_ctx_.Attach(sim_ctx_);
  vpi_ctx_.SetAtReadOnlySynchTime(true);
  vpiHandle h = vpi_handle_by_name(VpiText("cn"), nullptr);
  ASSERT_NE(h, nullptr);

  EXPECT_EQ(vpi_put_value(h, nullptr, nullptr, vpiCancelEvent), nullptr);
  s_vpi_error_info info = {};
  EXPECT_EQ(vpi_chk_error(&info), 0);
}

// §38.34: vpiReleaseFlag outside a run, with no net solver to hand the release
// to, clears the forced state the force set.
TEST_F(VpiPutValueSim, ReleaseOutsideARunClearsTheForce) {
  auto* var = sim_ctx_.CreateVariable("rr0", 8);
  var->value = MakeLogic4VecVal(arena_, 8, 0);
  VpiHandle arr = vpi_ctx_.CreateRegArray("rr", vpiStaticArray, {{0}}, {var});
  vpiHandle h = VpiHandleOf(arr->children[0]);

  s_vpi_value forced = {};
  forced.format = vpiIntVal;
  forced.value.integer = 6;
  vpi_put_value(h, &forced, nullptr, vpiForceFlag);
  ASSERT_TRUE(var->is_forced);
  s_vpi_value out = {};
  out.format = vpiIntVal;
  vpi_put_value(h, &out, nullptr, vpiReleaseFlag);
  EXPECT_FALSE(var->is_forced);
  EXPECT_EQ(out.value.integer, 6);
}

}  // namespace
}  // namespace delta
