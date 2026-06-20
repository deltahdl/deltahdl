#include <gtest/gtest.h>

#include <cstdint>
#include <vector>

#include "common/arena.h"
#include "simulator/scheduler.h"
#include "simulator/vpi.h"

namespace delta {
namespace {

class VpiPutDelaysSim : public ::testing::Test {
 protected:
  void SetUp() override {
    vpi_ctx_.SetScheduler(&scheduler_);
    SetGlobalVpiContext(&vpi_ctx_);
  }
  void TearDown() override { SetGlobalVpiContext(nullptr); }

  // Build a delay-bearing object of the given type carrying the supplied
  // delays, in source order. The handle is a VpiObject*, so the test sets the
  // category and seeds the stored delays directly.
  VpiHandle MakeDelayObject(int type, std::vector<VpiDelayInfo> delays) {
    VpiHandle obj = vpi_ctx_.CreateModule("u", "u");
    obj->type = type;
    obj->delays = std::move(delays);
    return obj;
  }

  Arena arena_;
  Scheduler scheduler_{arena_};
  VpiContext vpi_ctx_;
};

// §38.32 shall #1 + the "same order" rule: vpi_put_delays() sets the object's
// delays from the caller-allocated da array, one source value per delay (mtm
// and pulsere both off), in the order they occur in the source.
TEST_F(VpiPutDelaysSim, SetsDelaysInSourceOrder) {
  VpiHandle prim = MakeDelayObject(
      vpiPrimitive, {VpiDelayInfo{}, VpiDelayInfo{}, VpiDelayInfo{}});

  s_vpi_time da[3] = {};
  da[0].real = 11.0;
  da[1].real = 22.0;
  da[2].real = 33.0;
  s_vpi_delay delay = {};
  delay.da = da;
  delay.no_of_delays = 3;
  delay.time_type = vpiScaledRealTime;
  vpi_put_delays(prim, &delay);

  // Read the stored delays back via vpi_get_delays() to confirm they landed in
  // order.
  s_vpi_time out[3] = {};
  s_vpi_delay get = {};
  get.da = out;
  get.no_of_delays = 3;
  get.time_type = vpiScaledRealTime;
  vpi_get_delays(prim, &get);
  EXPECT_DOUBLE_EQ(out[0].real, 11.0);
  EXPECT_DOUBLE_EQ(out[1].real, 22.0);
  EXPECT_DOUBLE_EQ(out[2].real, 33.0);
}

// §38.32 shall #2: the form of the source values is controlled by the delay
// structure's time_type. A vpiSimTime put delivers the value as a 64-bit count
// split across high/low; the routine reconstitutes the same magnitude a
// vpiScaledRealTime put would have stored from the real field.
TEST_F(VpiPutDelaysSim, TimeTypeControlsSourceFormat) {
  VpiHandle prim =
      MakeDelayObject(vpiPrimitive, {VpiDelayInfo{}, VpiDelayInfo{}});

  s_vpi_time da[2] = {};
  da[0].low = 7u;  // vpiSimTime: value lives in high/low, not real
  da[1].low = 9u;
  s_vpi_delay delay = {};
  delay.da = da;
  delay.no_of_delays = 2;
  delay.time_type = vpiSimTime;
  vpi_put_delays(prim, &delay);

  s_vpi_time out[2] = {};
  s_vpi_delay get = {};
  get.da = out;
  get.no_of_delays = 2;
  get.time_type = vpiScaledRealTime;
  vpi_get_delays(prim, &get);
  EXPECT_DOUBLE_EQ(out[0].real, 7.0);
  EXPECT_DOUBLE_EQ(out[1].real, 9.0);
}

// §38.32 shall #3: if only the delay changes and not the pulse limits, the
// pulse limits retain the values they had before. A delay-only put (pulsere
// clear) overwrites the delay but leaves the stored reject/error limits intact.
TEST_F(VpiPutDelaysSim, DelayOnlyPutPreservesPulseLimits) {
  VpiDelayInfo seeded;
  seeded.delay = 1.0;
  seeded.reject = 40.0;
  seeded.error = 80.0;
  VpiHandle path = MakeDelayObject(vpiModPath, {seeded});

  // Put only the delay (pulsere_flag clear): one entry per delay.
  s_vpi_time da[1] = {};
  da[0].real = 99.0;
  s_vpi_delay delay = {};
  delay.da = da;
  delay.no_of_delays = 1;
  delay.time_type = vpiScaledRealTime;
  vpi_put_delays(path, &delay);

  // Read back with pulsere set: delay updated, reject/error unchanged.
  s_vpi_time out[3] = {};
  s_vpi_delay get = {};
  get.da = out;
  get.no_of_delays = 1;
  get.time_type = vpiScaledRealTime;
  get.pulsere_flag = 1;
  vpi_get_delays(path, &get);
  EXPECT_DOUBLE_EQ(out[0].real, 99.0);  // delay altered
  EXPECT_DOUBLE_EQ(out[1].real, 40.0);  // reject limit retained
  EXPECT_DOUBLE_EQ(out[2].real, 80.0);  // error limit retained
}

// §38.32 (Table 38-4, row 2): with mtm_flag set and pulsere_flag clear, each
// delay is taken from three source entries - min, then typ, then max delay.
TEST_F(VpiPutDelaysSim, MtmFlagConsumesMinTypMax) {
  VpiHandle prim =
      MakeDelayObject(vpiPrimitive, {VpiDelayInfo{}, VpiDelayInfo{}});

  // Two delays, three entries each (min:typ:max) -> six entries.
  s_vpi_time da[6] = {};
  for (int i = 0; i < 6; ++i) da[i].real = static_cast<double>(i + 1);
  s_vpi_delay delay = {};
  delay.da = da;
  delay.no_of_delays = 2;
  delay.time_type = vpiScaledRealTime;
  delay.mtm_flag = 1;
  vpi_put_delays(prim, &delay);

  s_vpi_time out[6] = {};
  s_vpi_delay get = {};
  get.da = out;
  get.no_of_delays = 2;
  get.time_type = vpiScaledRealTime;
  get.mtm_flag = 1;
  vpi_get_delays(prim, &get);
  for (int i = 0; i < 6; ++i)
    EXPECT_DOUBLE_EQ(out[i].real, static_cast<double>(i + 1)) << "entry " << i;
}

// §38.32 (Table 38-4, row 4): with both flags set each delay is taken from nine
// source entries - min:typ:max of the delay, then of the reject limit, then of
// the error limit, in that order.
TEST_F(VpiPutDelaysSim, MtmAndPulsereConsumeNineElements) {
  VpiHandle path = MakeDelayObject(vpiModPath, {VpiDelayInfo{}});

  s_vpi_time da[9] = {};
  for (int i = 0; i < 9; ++i) da[i].real = static_cast<double>(i + 1);
  s_vpi_delay delay = {};
  delay.da = da;
  delay.no_of_delays = 1;
  delay.time_type = vpiScaledRealTime;
  delay.mtm_flag = 1;
  delay.pulsere_flag = 1;
  vpi_put_delays(path, &delay);

  s_vpi_time out[9] = {};
  s_vpi_delay get = {};
  get.da = out;
  get.no_of_delays = 1;
  get.time_type = vpiScaledRealTime;
  get.mtm_flag = 1;
  get.pulsere_flag = 1;
  vpi_get_delays(path, &get);
  for (int i = 0; i < 9; ++i)
    EXPECT_DOUBLE_EQ(out[i].real, static_cast<double>(i + 1)) << "entry " << i;
}

// §38.32: the legal number of delays is fixed by the object's category. A
// primitive accepts 2 or 3; an illegal request (here 4) is rejected with an
// error recorded (§38.2) and the stored delays left unchanged.
TEST_F(VpiPutDelaysSim, IllegalNoOfDelaysIsRejected) {
  VpiDelayInfo seeded;
  seeded.delay = 5.0;
  VpiHandle prim =
      MakeDelayObject(vpiPrimitive, {seeded, seeded, seeded, seeded});

  s_vpi_time da[4] = {};
  for (int i = 0; i < 4; ++i) da[i].real = 1000.0;
  s_vpi_delay delay = {};
  delay.da = da;
  delay.no_of_delays = 4;  // not 2 or 3 -> illegal for a primitive
  delay.time_type = vpiScaledRealTime;
  vpi_put_delays(prim, &delay);

  EXPECT_EQ(vpi_ctx_.LastError().level, kVpiError);

  // The stored delays were not altered by the rejected request.
  s_vpi_time out[3] = {};
  s_vpi_delay get = {};
  get.da = out;
  get.no_of_delays = 3;
  get.time_type = vpiScaledRealTime;
  vpi_get_delays(prim, &get);
  EXPECT_DOUBLE_EQ(out[0].real, 5.0);  // unchanged seed
}

// §38.32 / §38.1: the structure and its da array are application-allocated, so
// a null structure, a null da, or a null handle leaves nothing to do and must
// be safe.
TEST_F(VpiPutDelaysSim, NullArgumentsAreSafe) {
  VpiDelayInfo d;
  d.delay = 1.0;
  VpiHandle prim = MakeDelayObject(vpiPrimitive, {d, d});

  vpi_put_delays(prim, nullptr);  // null structure

  s_vpi_delay no_array = {};
  no_array.no_of_delays = 2;
  no_array.time_type = vpiScaledRealTime;
  vpi_put_delays(prim, &no_array);  // null da

  s_vpi_time da[2] = {};
  s_vpi_delay delay = {};
  delay.da = da;
  delay.no_of_delays = 2;
  delay.time_type = vpiScaledRealTime;
  vpi_put_delays(nullptr, &delay);  // null handle

  SUCCEED();
}

// §38.32 (Table 38-4, row 3): with pulsere_flag set and mtm_flag clear, each
// delay is taken from three source entries - the delay, the reject limit, and
// the error limit. This exercises the pulse-limits-only layout branch on the
// write path.
TEST_F(VpiPutDelaysSim, PulsereOnlyPutConsumesDelayRejectError) {
  VpiHandle path = MakeDelayObject(vpiModPath, {VpiDelayInfo{}});

  s_vpi_time da[3] = {};
  da[0].real = 10.0;  // delay
  da[1].real = 4.0;   // reject limit
  da[2].real = 8.0;   // error limit
  s_vpi_delay delay = {};
  delay.da = da;
  delay.no_of_delays = 1;
  delay.time_type = vpiScaledRealTime;
  delay.pulsere_flag = 1;
  vpi_put_delays(path, &delay);

  s_vpi_time out[3] = {};
  s_vpi_delay get = {};
  get.da = out;
  get.no_of_delays = 1;
  get.time_type = vpiScaledRealTime;
  get.pulsere_flag = 1;
  vpi_get_delays(path, &get);
  EXPECT_DOUBLE_EQ(out[0].real, 10.0);
  EXPECT_DOUBLE_EQ(out[1].real, 4.0);
  EXPECT_DOUBLE_EQ(out[2].real, 8.0);
}

// §38.32 (N6, timing-check category): for a timing check the legal number of
// delays must match the number of limits the check actually has. A matching
// count is honored; a mismatching count is rejected with an error (§38.2) and
// the stored limits are left unchanged.
TEST_F(VpiPutDelaysSim, TimingCheckRequiresMatchingLimitCount) {
  VpiDelayInfo a;
  a.delay = 2.0;
  VpiDelayInfo b;
  b.delay = 4.0;
  VpiHandle tchk = MakeDelayObject(vpiTchk, {a, b});  // two limits

  // A count matching the limit count is accepted.
  s_vpi_time da[2] = {};
  da[0].real = 20.0;
  da[1].real = 40.0;
  s_vpi_delay delay = {};
  delay.da = da;
  delay.no_of_delays = 2;
  delay.time_type = vpiScaledRealTime;
  vpi_put_delays(tchk, &delay);
  EXPECT_EQ(vpi_ctx_.LastError().level, 0);

  s_vpi_time out[2] = {};
  s_vpi_delay get = {};
  get.da = out;
  get.no_of_delays = 2;
  get.time_type = vpiScaledRealTime;
  vpi_get_delays(tchk, &get);
  EXPECT_DOUBLE_EQ(out[0].real, 20.0);
  EXPECT_DOUBLE_EQ(out[1].real, 40.0);

  // A count that does not match the number of limits is rejected.
  vpi_ctx_.ResetErrorStatus();
  s_vpi_time bad[3] = {};
  for (int i = 0; i < 3; ++i) bad[i].real = 999.0;
  s_vpi_delay bad_delay = {};
  bad_delay.da = bad;
  bad_delay.no_of_delays = 3;  // does not match the two limits
  bad_delay.time_type = vpiScaledRealTime;
  vpi_put_delays(tchk, &bad_delay);
  EXPECT_EQ(vpi_ctx_.LastError().level, kVpiError);

  // The earlier values survive the rejected request.
  vpi_ctx_.ResetErrorStatus();
  s_vpi_time after[2] = {};
  s_vpi_delay after_get = {};
  after_get.da = after;
  after_get.no_of_delays = 2;
  after_get.time_type = vpiScaledRealTime;
  vpi_get_delays(tchk, &after_get);
  EXPECT_DOUBLE_EQ(after[0].real, 20.0);
  EXPECT_DOUBLE_EQ(after[1].real, 40.0);
}

// §38.32 (N6, intermodule-path category): an intermodule path accepts 2 or 3
// delays. A legal count is honored; the values land in source order.
TEST_F(VpiPutDelaysSim, IntermodulePathAcceptsTwoOrThree) {
  VpiHandle imp =
      MakeDelayObject(vpiInterModPath, {VpiDelayInfo{}, VpiDelayInfo{}});

  s_vpi_time da[2] = {};
  da[0].real = 12.0;
  da[1].real = 34.0;
  s_vpi_delay delay = {};
  delay.da = da;
  delay.no_of_delays = 2;
  delay.time_type = vpiScaledRealTime;
  vpi_put_delays(imp, &delay);
  EXPECT_EQ(vpi_ctx_.LastError().level, 0);

  s_vpi_time out[2] = {};
  s_vpi_delay get = {};
  get.da = out;
  get.no_of_delays = 2;
  get.time_type = vpiScaledRealTime;
  vpi_get_delays(imp, &get);
  EXPECT_DOUBLE_EQ(out[0].real, 12.0);
  EXPECT_DOUBLE_EQ(out[1].real, 34.0);
}

}  // namespace
}  // namespace delta
