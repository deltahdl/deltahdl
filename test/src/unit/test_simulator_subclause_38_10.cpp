#include <gtest/gtest.h>

#include <cstdint>

#include "common/arena.h"
#include "helpers_vpi_delays_fixture.h"
#include "simulator/scheduler.h"
#include "simulator/vpi.h"

namespace delta {
namespace {

using VpiGetDelaysSim = VpiDelaysSimBase;

// §38.10 shall #1 + the "same order" rule: vpi_get_delays() places the object's
// delays into the caller-allocated da array, one entry per delay (mtm and
// pulsere both off), in the order they occur in the source.
TEST_F(VpiGetDelaysSim, RetrievesDelaysInSourceOrder) {
  VpiDelayInfo d0;
  d0.delay = 11.0;
  VpiDelayInfo d1;
  d1.delay = 22.0;
  VpiDelayInfo d2;
  d2.delay = 33.0;
  VpiHandle prim = MakeDelayObject(vpiPrimitive, {d0, d1, d2});

  s_vpi_time da[3] = {};
  s_vpi_delay delay = {};
  delay.da = da;
  delay.no_of_delays = 3;
  delay.time_type = vpiScaledRealTime;
  vpi_get_delays(prim, &delay);

  EXPECT_DOUBLE_EQ(da[0].real, 11.0);
  EXPECT_DOUBLE_EQ(da[1].real, 22.0);
  EXPECT_DOUBLE_EQ(da[2].real, 33.0);
}

// §38.10 shall #2: the form of the delay information is controlled by the
// delay structure's time_type. At the same data, vpiScaledRealTime fills the
// real field while vpiSimTime fills the high/low 64-bit halves.
TEST_F(VpiGetDelaysSim, TimeTypeControlsFormat) {
  VpiDelayInfo d;
  d.delay = 7.0;
  VpiHandle prim = MakeDelayObject(vpiPrimitive, {d, d});

  s_vpi_time as_real[2] = {};
  s_vpi_delay real_delay = {};
  real_delay.da = as_real;
  real_delay.no_of_delays = 2;
  real_delay.time_type = vpiScaledRealTime;
  vpi_get_delays(prim, &real_delay);
  EXPECT_DOUBLE_EQ(as_real[0].real, 7.0);
  EXPECT_EQ(as_real[0].low, 0u);

  s_vpi_time as_sim[2] = {};
  s_vpi_delay sim_delay = {};
  sim_delay.da = as_sim;
  sim_delay.no_of_delays = 2;
  sim_delay.time_type = vpiSimTime;
  vpi_get_delays(prim, &sim_delay);
  EXPECT_EQ(as_sim[0].low, 7u);
  EXPECT_DOUBLE_EQ(as_sim[0].real, 0.0);
}

// §38.10 shall #2 (edge): a time_type of vpiSuppressTime asks for no time
// value. The routine still stamps the entry's type, but leaves the value
// cleared even though the object carries a nonzero delay.
TEST_F(VpiGetDelaysSim, SuppressTimeTypeYieldsNoTimeValue) {
  VpiDelayInfo d;
  d.delay = 7.0;
  VpiHandle prim = MakeDelayObject(vpiPrimitive, {d, d});

  s_vpi_time da[2] = {};
  s_vpi_delay delay = {};
  delay.da = da;
  delay.no_of_delays = 2;
  delay.time_type = vpiSuppressTime;
  vpi_get_delays(prim, &delay);

  EXPECT_EQ(da[0].type, vpiSuppressTime);
  EXPECT_DOUBLE_EQ(da[0].real, 0.0);  // suppressed despite the stored 7.0
  EXPECT_EQ(da[0].low, 0u);
  EXPECT_EQ(da[0].high, 0u);
}

// §38.10 shall #3: the routine ignores the value of the type flag in each
// s_vpi_time entry. A garbage type on input is overwritten with the delay
// structure's time_type, and the value is formatted accordingly.
TEST_F(VpiGetDelaysSim, IgnoresInputEntryTypeFlag) {
  VpiDelayInfo d;
  d.delay = 5.0;
  VpiHandle prim = MakeDelayObject(vpiPrimitive, {d, d});

  s_vpi_time da[2] = {};
  da[0].type = 999;  // bogus per-entry type that must be ignored
  da[1].type = -42;
  s_vpi_delay delay = {};
  delay.da = da;
  delay.no_of_delays = 2;
  delay.time_type = vpiScaledRealTime;
  vpi_get_delays(prim, &delay);

  EXPECT_EQ(da[0].type, vpiScaledRealTime);
  EXPECT_EQ(da[1].type, vpiScaledRealTime);
  EXPECT_DOUBLE_EQ(da[0].real, 5.0);
}

// §38.10 (Table 38-2, row 2): with mtm_flag set and pulsere_flag clear, each
// delay occupies three entries - min, then typ, then max delay.
TEST_F(VpiGetDelaysSim, MtmFlagExpandsToMinTypMax) {
  VpiDelayInfo d;
  d.min_delay = 1.0;
  d.typ_delay = 2.0;
  d.max_delay = 3.0;
  VpiHandle prim = MakeDelayObject(vpiPrimitive, {d, d});  // no_of_delays = 2

  // Two delays, three entries each (min:typ:max) -> six entries.
  s_vpi_time wide[6] = {};
  s_vpi_delay delay = {};
  delay.da = wide;
  delay.no_of_delays = 2;  // legal for a primitive (2 or 3)
  delay.time_type = vpiScaledRealTime;
  delay.mtm_flag = 1;
  vpi_get_delays(prim, &delay);

  EXPECT_DOUBLE_EQ(wide[0].real, 1.0);
  EXPECT_DOUBLE_EQ(wide[1].real, 2.0);
  EXPECT_DOUBLE_EQ(wide[2].real, 3.0);
  // Second delay's run starts at index 3.
  EXPECT_DOUBLE_EQ(wide[3].real, 1.0);
}

// §38.10 (Table 38-2, row 3): with pulsere_flag set and mtm_flag clear, each
// delay occupies three entries - the delay, the reject limit, and the error
// limit.
TEST_F(VpiGetDelaysSim, PulsereFlagExpandsToDelayRejectError) {
  VpiDelayInfo d;
  d.delay = 10.0;
  d.reject = 4.0;
  d.error = 8.0;
  VpiHandle path = MakeDelayObject(vpiModPath, {d});  // no_of_delays = 1 legal

  s_vpi_time da[3] = {};
  s_vpi_delay delay = {};
  delay.da = da;
  delay.no_of_delays = 1;
  delay.time_type = vpiScaledRealTime;
  delay.pulsere_flag = 1;
  vpi_get_delays(path, &delay);

  EXPECT_DOUBLE_EQ(da[0].real, 10.0);
  EXPECT_DOUBLE_EQ(da[1].real, 4.0);
  EXPECT_DOUBLE_EQ(da[2].real, 8.0);
}

// §38.10 (Table 38-2, row 4): with both flags set each delay occupies nine
// entries - min:typ:max of the delay, then of the reject limit, then of the
// error limit, in that order.
TEST_F(VpiGetDelaysSim, MtmAndPulsereExpandToNineElements) {
  VpiDelayInfo d;
  d.min_delay = 1.0;
  d.typ_delay = 2.0;
  d.max_delay = 3.0;
  d.min_reject = 4.0;
  d.typ_reject = 5.0;
  d.max_reject = 6.0;
  d.min_error = 7.0;
  d.typ_error = 8.0;
  d.max_error = 9.0;
  VpiHandle path = MakeDelayObject(vpiModPath, {d});

  s_vpi_time da[9] = {};
  s_vpi_delay delay = {};
  delay.da = da;
  delay.no_of_delays = 1;
  delay.time_type = vpiScaledRealTime;
  delay.mtm_flag = 1;
  delay.pulsere_flag = 1;
  vpi_get_delays(path, &delay);

  for (int i = 0; i < 9; ++i) {
    EXPECT_DOUBLE_EQ(da[i].real, static_cast<double>(i + 1)) << "entry " << i;
  }
}

// §38.10: the legal number of delays is fixed by the object's category. A
// primitive accepts 2 or 3; an illegal request (here 4) is rejected with an
// error recorded and the caller's array left untouched.
TEST_F(VpiGetDelaysSim, IllegalNoOfDelaysForPrimitiveIsRejected) {
  VpiDelayInfo d;
  d.delay = 1.0;
  VpiHandle prim = MakeDelayObject(vpiPrimitive, {d, d, d, d});

  s_vpi_time da[4] = {};
  da[0].real = -1.0;  // sentinel that must survive an unfilled call
  s_vpi_delay delay = {};
  delay.da = da;
  delay.no_of_delays = 4;  // not 2 or 3 -> illegal for a primitive
  delay.time_type = vpiScaledRealTime;
  vpi_get_delays(prim, &delay);

  EXPECT_EQ(vpi_ctx_.LastError().level, kVpiError);
  EXPECT_DOUBLE_EQ(da[0].real, -1.0);  // untouched
}

// §38.10: for a timing check the legal number of delays must match the number
// of limits the check actually has. A request matching the stored limit count
// is honored.
TEST_F(VpiGetDelaysSim, TimingCheckNoOfDelaysMatchesLimitCount) {
  VpiDelayInfo a;
  a.delay = 2.0;
  VpiDelayInfo b;
  b.delay = 4.0;
  VpiHandle tchk = MakeDelayObject(vpiTchk, {a, b});  // two limits

  s_vpi_time da[2] = {};
  s_vpi_delay delay = {};
  delay.da = da;
  delay.no_of_delays = 2;  // matches the two limits
  delay.time_type = vpiScaledRealTime;
  vpi_get_delays(tchk, &delay);

  EXPECT_EQ(vpi_ctx_.LastError().level, 0);
  EXPECT_DOUBLE_EQ(da[0].real, 2.0);
  EXPECT_DOUBLE_EQ(da[1].real, 4.0);

  // A count that does not match the number of limits is rejected.
  vpi_ctx_.ResetErrorStatus();
  s_vpi_time bad[3] = {};
  s_vpi_delay bad_delay = {};
  bad_delay.da = bad;
  bad_delay.no_of_delays = 3;
  bad_delay.time_type = vpiScaledRealTime;
  vpi_get_delays(tchk, &bad_delay);
  EXPECT_EQ(vpi_ctx_.LastError().level, kVpiError);
}

// §38.10: an intermodule path accepts 2 or 3 delays. The handle reads back its
// stored delays in order when the count is legal.
TEST_F(VpiGetDelaysSim, IntermodulePathAcceptsTwoOrThree) {
  VpiDelayInfo a;
  a.delay = 12.0;
  VpiDelayInfo b;
  b.delay = 34.0;
  VpiHandle imp = MakeDelayObject(vpiInterModPath, {a, b});

  s_vpi_time da[2] = {};
  s_vpi_delay delay = {};
  delay.da = da;
  delay.no_of_delays = 2;
  delay.time_type = vpiScaledRealTime;
  vpi_get_delays(imp, &delay);

  EXPECT_EQ(vpi_ctx_.LastError().level, 0);
  EXPECT_DOUBLE_EQ(da[0].real, 12.0);
  EXPECT_DOUBLE_EQ(da[1].real, 34.0);
}

// §38.10: a path-delay (module path) object has its own legal set of delay
// counts - 1, 2, 3, 6, or 12 - distinct from the other categories. A count in
// that set (here 6) is honored; a count outside it (here 4) is rejected with an
// error and the array left untouched.
TEST_F(VpiGetDelaysSim, ModulePathLegalSetAcceptsSixRejectsFour) {
  std::vector<VpiDelayInfo> six;
  for (int i = 0; i < 6; ++i) {
    VpiDelayInfo d;
    d.delay = static_cast<double>(i + 1);
    six.push_back(d);
  }
  VpiHandle path = MakeDelayObject(vpiModPath, six);

  s_vpi_time da[6] = {};
  s_vpi_delay delay = {};
  delay.da = da;
  delay.no_of_delays = 6;  // in {1,2,3,6,12} -> legal for a module path
  delay.time_type = vpiScaledRealTime;
  vpi_get_delays(path, &delay);

  EXPECT_EQ(vpi_ctx_.LastError().level, 0);
  for (int i = 0; i < 6; ++i) {
    EXPECT_DOUBLE_EQ(da[i].real, static_cast<double>(i + 1)) << "entry " << i;
  }

  // 4 is not in the path-delay legal set, so the request is rejected.
  vpi_ctx_.ResetErrorStatus();
  s_vpi_time bad[4] = {};
  bad[0].real = -1.0;  // sentinel that must survive an unfilled call
  s_vpi_delay bad_delay = {};
  bad_delay.da = bad;
  bad_delay.no_of_delays = 4;
  bad_delay.time_type = vpiScaledRealTime;
  vpi_get_delays(path, &bad_delay);

  EXPECT_EQ(vpi_ctx_.LastError().level, kVpiError);
  EXPECT_DOUBLE_EQ(bad[0].real, -1.0);  // untouched
}

// §38.10 / §38.1: the structure and its da array are application-allocated, so
// the routine fills the caller's memory in place and a null destination (or a
// null da, or a null handle) leaves nothing to do and must be safe.
TEST_F(VpiGetDelaysSim, NullArgumentsAreSafe) {
  VpiDelayInfo d;
  d.delay = 1.0;
  VpiHandle prim = MakeDelayObject(vpiPrimitive, {d, d});

  vpi_get_delays(prim, nullptr);  // null structure

  s_vpi_delay no_array = {};
  no_array.no_of_delays = 2;
  no_array.time_type = vpiScaledRealTime;
  vpi_get_delays(prim, &no_array);  // null da

  s_vpi_time da[2] = {};
  s_vpi_delay delay = {};
  delay.da = da;
  delay.no_of_delays = 2;
  delay.time_type = vpiScaledRealTime;
  vpi_get_delays(nullptr, &delay);  // null handle

  SUCCEED();
}

}  // namespace
}  // namespace delta
