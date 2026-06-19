#include <gtest/gtest.h>

#include <cstdint>

#include "common/arena.h"
#include "common/types.h"
#include "simulator/scheduler.h"
#include "simulator/vpi.h"

// Annex H.13 functions under test. They belong to the DPI C layer (svdpi.cpp)
// and are declared in svdpi.h, but svdpi.h cannot be included in this
// translation unit: it spells the time-form constants vpiSimTime and
// vpiScaledRealTime with the two swapped relative to vpi.h, and redefines
// s_vpi_time, which this test needs from vpi.h to build the simulation-time
// state and to compare against vpi_get(). H.13 states that svTimeVal is "fully
// equivalent to s_vpi_time", so the layout-identical delta::VpiTime stands in
// for svTimeVal across the C ABI; driving svGetTime through it also exercises
// that equivalence.
extern "C" {
int svGetTime(const void* scope, delta::VpiTime* time);
int svGetTimeUnit(const void* scope, int32_t* time_unit);
int svGetTimePrecision(const void* scope, int32_t* time_precision);
}

namespace delta {
namespace {

// svdpi.h encodes the requested time form in svTimeVal.type. These are its
// values (sv_scaled_real_time and sv_sim_time); vpi.h spells the same two names
// swapped, so the field must be set with svdpi.h's encoding for svGetTime to
// interpret the request the way the standard svdpi.h does.
constexpr int kSvScaledRealTime = 1;
constexpr int kSvSimTime = 2;

class SvGetTimeSim : public ::testing::Test {
 protected:
  void SetUp() override {
    vpi_ctx_.SetScheduler(&scheduler_);
    SetGlobalVpiContext(&vpi_ctx_);
  }
  void TearDown() override { SetGlobalVpiContext(nullptr); }

  // Advance the simulation clock to `t` by draining a no-op event scheduled
  // there; after Run() the scheduler's current time is that slot.
  void AdvanceTo(uint64_t t) {
    auto* ev = scheduler_.GetEventPool().Acquire();
    ev->callback = []() {};
    scheduler_.ScheduleEvent(SimTime{t}, Region::kActive, ev);
    scheduler_.Run();
  }

  Arena arena_;
  Scheduler scheduler_{arena_};
  VpiContext vpi_ctx_;
};

// §H.13: svGetTime retrieves the current simulation time. With a null scope the
// time is read in the simulation time unit; a sim-time request delivers the full
// 64-bit count split across the high and low halves. Reaching the current
// scheduler time through svGetTime is the rule being applied.
TEST_F(SvGetTimeSim, NullScopeRetrievesCurrentSimulationTime) {
  const uint64_t ticks = (static_cast<uint64_t>(3) << 32) | 5u;
  AdvanceTo(ticks);

  VpiTime t = {};
  t.type = kSvSimTime;
  EXPECT_EQ(svGetTime(nullptr, &t), 0);
  EXPECT_EQ(t.high, 3u);
  EXPECT_EQ(t.low, 5u);
}

// §H.13: the type field of the svTimeVal shall select whether scaled real or
// simulation time is delivered. At the same instant a sim-time request fills
// high/low and leaves real zero, while a scaled-real request fills real and
// leaves high/low zero.
TEST_F(SvGetTimeSim, TypeFieldSelectsSimVersusScaledReal) {
  AdvanceTo(7);

  VpiTime as_sim = {};
  as_sim.type = kSvSimTime;
  EXPECT_EQ(svGetTime(nullptr, &as_sim), 0);
  EXPECT_EQ(as_sim.low, 7u);
  EXPECT_DOUBLE_EQ(as_sim.real, 0.0);

  VpiTime as_real = {};
  as_real.type = kSvScaledRealTime;
  EXPECT_EQ(svGetTime(nullptr, &as_real), 0);
  EXPECT_DOUBLE_EQ(as_real.real, 7.0);
  EXPECT_EQ(as_real.low, 0u);
}

// §H.13: calling svGetTime with a null scope retrieves the current time scaled
// to the simulation time unit. With the simulation counting picoseconds and no
// per-scope timescale applied, the scaled-real result equals the raw count
// rather than being rescaled to any object's unit.
TEST_F(SvGetTimeSim, NullScopeScalesToSimulationTimeUnit) {
  vpi_ctx_.SetSimTimeUnit(-12);  // simulation counts in 1 ps
  AdvanceTo(1000);

  VpiTime t = {};
  t.type = kSvScaledRealTime;
  EXPECT_EQ(svGetTime(nullptr, &t), 0);
  EXPECT_DOUBLE_EQ(t.real, 1000.0);
}

// §H.13: svGetTimeUnit with a null scope retrieves the simulation time unit, and
// the value it returns is equivalent to vpi_get(vpiTimeUnit) for the design.
TEST_F(SvGetTimeSim, TimeUnitMatchesVpiGetForNullScope) {
  vpiHandle top = vpi_ctx_.CreateModule("top", "top");
  ASSERT_NE(top, nullptr);
  top->time_precision = -9;

  int32_t unit = 12345;  // sentinel; overwritten on success
  EXPECT_EQ(svGetTimeUnit(nullptr, &unit), 0);
  EXPECT_EQ(unit, vpi_get(vpiTimeUnit, nullptr));
}

// §H.13: svGetTimePrecision with a null scope behaves likewise, returning a
// value equivalent to vpi_get(vpiTimePrecision) for the design.
TEST_F(SvGetTimeSim, TimePrecisionMatchesVpiGetForNullScope) {
  vpiHandle top = vpi_ctx_.CreateModule("top", "top");
  ASSERT_NE(top, nullptr);
  top->time_precision = -12;

  int32_t prec = 999;  // sentinel; overwritten on success
  EXPECT_EQ(svGetTimePrecision(nullptr, &prec), 0);
  EXPECT_EQ(prec, vpi_get(vpiTimePrecision, nullptr));
}

// §H.13: svGetTime is defined to scale to the time unit of the instance scope
// associated with the supplied svScope; the null-scope case is the special form
// that uses the simulation time unit. This simulator binds no per-scope timescale
// to an svScope, so a non-null scope resolves to the same design-wide simulation
// time. Driving the non-null-scope path confirms production accepts the scope
// argument and routes it to the shared time source rather than rejecting it.
TEST_F(SvGetTimeSim, NonNullScopeRetrievesCurrentSimulationTime) {
  AdvanceTo(42);

  int marker = 0;
  const void* scope = &marker;  // non-null svScope; no per-scope timescale bound

  VpiTime with_scope = {};
  with_scope.type = kSvSimTime;
  EXPECT_EQ(svGetTime(scope, &with_scope), 0);

  VpiTime null_scope = {};
  null_scope.type = kSvSimTime;
  EXPECT_EQ(svGetTime(nullptr, &null_scope), 0);

  EXPECT_EQ(with_scope.low, 42u);
  EXPECT_EQ(with_scope.high, null_scope.high);
  EXPECT_EQ(with_scope.low, null_scope.low);
}

// §H.13: svGetTimeUnit and svGetTimePrecision are likewise defined per the
// instance scope associated with an svScope, with the null scope as the
// simulation-time-unit special form. With no per-scope timescale binding a
// non-null scope yields the same unit and precision the null scope does;
// exercising the non-null path confirms both routines honor the scope argument.
TEST_F(SvGetTimeSim, NonNullScopeUnitAndPrecisionMatchNullScope) {
  vpiHandle top = vpi_ctx_.CreateModule("top", "top");
  ASSERT_NE(top, nullptr);
  top->time_precision = -9;

  int marker = 0;
  const void* scope = &marker;  // non-null svScope

  int32_t unit_scoped = 0;
  int32_t unit_null = 0;
  EXPECT_EQ(svGetTimeUnit(scope, &unit_scoped), 0);
  EXPECT_EQ(svGetTimeUnit(nullptr, &unit_null), 0);
  EXPECT_EQ(unit_scoped, unit_null);

  int32_t prec_scoped = 0;
  int32_t prec_null = 0;
  EXPECT_EQ(svGetTimePrecision(scope, &prec_scoped), 0);
  EXPECT_EQ(svGetTimePrecision(nullptr, &prec_null), 0);
  EXPECT_EQ(prec_scoped, prec_null);
}

// §H.13 / Annex I: each routine reports failure when there is nowhere to write
// the result, returning -1 rather than touching unowned memory.
TEST_F(SvGetTimeSim, NullDestinationReturnsError) {
  AdvanceTo(4);
  EXPECT_EQ(svGetTime(nullptr, nullptr), -1);
  EXPECT_EQ(svGetTimeUnit(nullptr, nullptr), -1);
  EXPECT_EQ(svGetTimePrecision(nullptr, nullptr), -1);
}

}  // namespace
}  // namespace delta
