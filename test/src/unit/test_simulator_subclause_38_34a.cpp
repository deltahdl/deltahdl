#include <gtest/gtest.h>

#include <cstdint>

#include "common/arena.h"
#include "common/diagnostic.h"
#include "common/source_mgr.h"
#include "common/types.h"
#include "simulator/net.h"
#include "simulator/sim_context.h"
#include "simulator/sv_vpi_user.h"
#include "simulator/variable.h"
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
  EXPECT_EQ(net->resolved->value.ToUint64(), 123u);

  net->drivers.push_back(MakeLogic4VecVal(arena_, 32, 5));
  net->Resolve(arena_);
  EXPECT_EQ(net->resolved->value.ToUint64(), 5u);
}

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

  vpi_put_value(ev, nullptr, nullptr, vpiCancelEvent);
  s_vpi_error_info info = {};
  vpi_put_value(ev, nullptr, nullptr, vpiCancelEvent);
  EXPECT_EQ(vpi_chk_error(&info), 0);
  EXPECT_EQ(vpi_get(vpiScheduled, ev), 0);
}

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

TEST_F(VpiPutValueSim, SequentialUdpRejectsDelayMode) {
  auto* var = sim_ctx_.CreateVariable("up", 1);
  var->value = MakeLogic4VecVal(arena_, 1, 0);
  vpi_ctx_.Attach(sim_ctx_);

  vpiHandle h = vpi_handle_by_name(VpiText("up"), nullptr);
  ASSERT_NE(h, nullptr);
  VpiObjectOf(h)->type = vpiUdp;
  VpiObjectOf(h)->prim_type = vpiSeqPrim;

  s_vpi_value val = {};
  val.format = vpiScalarVal;
  val.value.scalar = vpi1;
  s_vpi_time time = {};
  time.type = vpiSimTime;
  time.low = 3;
  vpi_put_value(h, &val, &time, vpiTransportDelay);

  s_vpi_error_info info = {};
  EXPECT_EQ(vpi_chk_error(&info), vpiError);
  EXPECT_EQ(var->value.words[0].aval & 1, 0u);
}

TEST_F(VpiPutValueSim, SequentialUdpRejectsPureTransportDelay) {
  auto* var = sim_ctx_.CreateVariable("uq", 1);
  var->value = MakeLogic4VecVal(arena_, 1, 0);
  vpi_ctx_.Attach(sim_ctx_);

  vpiHandle h = vpi_handle_by_name(VpiText("uq"), nullptr);
  ASSERT_NE(h, nullptr);
  VpiObjectOf(h)->type = vpiUdp;
  VpiObjectOf(h)->prim_type = vpiSeqPrim;

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

TEST_F(VpiPutValueSim, SequentialUdpRejectsInertialDelay) {
  auto* var = sim_ctx_.CreateVariable("ui", 1);
  var->value = MakeLogic4VecVal(arena_, 1, 0);
  vpi_ctx_.Attach(sim_ctx_);

  vpiHandle h = vpi_handle_by_name(VpiText("ui"), nullptr);
  ASSERT_NE(h, nullptr);
  VpiObjectOf(h)->type = vpiUdp;
  VpiObjectOf(h)->prim_type = vpiSeqPrim;

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

TEST_F(VpiPutValueSim, SequentialUdpAcceptsNoDelay) {
  auto* var = sim_ctx_.CreateVariable("ua", 1);
  var->value = MakeLogic4VecVal(arena_, 1, 0);
  vpi_ctx_.Attach(sim_ctx_);

  vpiHandle h = vpi_handle_by_name(VpiText("ua"), nullptr);
  ASSERT_NE(h, nullptr);
  VpiObjectOf(h)->type = vpiUdp;
  VpiObjectOf(h)->prim_type = vpiSeqPrim;

  s_vpi_value val = {};
  val.format = vpiScalarVal;
  val.value.scalar = vpi1;
  vpi_put_value(h, &val, nullptr, vpiNoDelay);

  s_vpi_error_info info = {};
  EXPECT_EQ(vpi_chk_error(&info), 0);
  EXPECT_EQ(var->value.words[0].aval & 1, 1u);
}

class VpiPutValueFormats : public VpiPutValueSim {
 protected:
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
  val.value.str = VpiText("18446744073709551621");
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

TEST_F(VpiPutValueSim, AnEventPutWithNoRunStampsItsTriggerTime) {
  Variable event;
  event.is_event = true;
  VpiObject obj;
  obj.type = vpiNamedEvent;
  obj.var = &event;
  vpi_ctx_.SetScheduler(&scheduler_);
  EXPECT_EQ(vpi_put_value(VpiHandleOf(&obj), nullptr, nullptr, vpiNoDelay),
            nullptr);
  EXPECT_EQ(event.triggered_ticks, scheduler_.CurrentTime().ticks);
}

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
  s_vpi_time zero = {};
  zero.type = vpiSimTime;
  EXPECT_EQ(vpi_put_value(h, &val, &zero, kFlags), nullptr);
}

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
