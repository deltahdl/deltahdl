#include <gtest/gtest.h>

#include <cstdint>

#include "common/arena.h"
#include "common/types.h"
#include "simulator/dpi_runtime.h"
#include "simulator/scheduler.h"
#include "simulator/vpi_context.h"
#include "simulator/vpi_globals.h"
#include "simulator/vpi_object.h"
#include "simulator/vpi_user.h"

extern "C" {
int svGetTime(const void* scope, s_vpi_time* time);
int svGetTimeUnit(const void* scope, int32_t* time_unit);
int svGetTimePrecision(const void* scope, int32_t* time_precision);
}

namespace delta {
namespace {

constexpr int kSvScaledRealTime = vpiScaledRealTime;
constexpr int kSvSimTime = vpiSimTime;

class SvGetTimeSim : public ::testing::Test {
 protected:
  void SetUp() override {
    vpi_ctx_.SetScheduler(&scheduler_);
    SetGlobalVpiContext(&vpi_ctx_);
  }
  void TearDown() override { SetGlobalVpiContext(nullptr); }

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

TEST_F(SvGetTimeSim, NullScopeRetrievesCurrentSimulationTime) {
  const uint64_t kTicks = (static_cast<uint64_t>(3) << 32) | 5u;
  AdvanceTo(kTicks);

  s_vpi_time t = {};
  t.type = kSvSimTime;
  EXPECT_EQ(svGetTime(nullptr, &t), 0);
  EXPECT_EQ(t.high, 3u);
  EXPECT_EQ(t.low, 5u);
}

TEST_F(SvGetTimeSim, TypeFieldSelectsSimVersusScaledReal) {
  AdvanceTo(7);

  s_vpi_time as_sim = {};
  as_sim.type = kSvSimTime;
  EXPECT_EQ(svGetTime(nullptr, &as_sim), 0);
  EXPECT_EQ(as_sim.low, 7u);
  EXPECT_DOUBLE_EQ(as_sim.real, 0.0);

  s_vpi_time as_real = {};
  as_real.type = kSvScaledRealTime;
  EXPECT_EQ(svGetTime(nullptr, &as_real), 0);
  EXPECT_DOUBLE_EQ(as_real.real, 7.0);
  EXPECT_EQ(as_real.low, 0u);
}

TEST_F(SvGetTimeSim, NullScopeScalesToSimulationTimeUnit) {
  vpi_ctx_.SetSimTimeUnit(-12);
  AdvanceTo(1000);

  s_vpi_time t = {};
  t.type = kSvScaledRealTime;
  EXPECT_EQ(svGetTime(nullptr, &t), 0);
  EXPECT_DOUBLE_EQ(t.real, 1000.0);
}

TEST_F(SvGetTimeSim, TimeUnitMatchesVpiGetForNullScope) {
  VpiHandle top = vpi_ctx_.CreateModule("top", "top");
  ASSERT_NE(top, nullptr);
  top->time_precision = -9;

  int32_t unit = 12345;
  EXPECT_EQ(svGetTimeUnit(nullptr, &unit), 0);
  EXPECT_EQ(unit, vpi_get(vpiTimeUnit, nullptr));
}

TEST_F(SvGetTimeSim, TimePrecisionMatchesVpiGetForNullScope) {
  VpiHandle top = vpi_ctx_.CreateModule("top", "top");
  ASSERT_NE(top, nullptr);
  top->time_precision = -12;

  int32_t prec = 999;
  EXPECT_EQ(svGetTimePrecision(nullptr, &prec), 0);
  EXPECT_EQ(prec, vpi_get(vpiTimePrecision, nullptr));
}

TEST_F(SvGetTimeSim, NonNullScopeRetrievesCurrentSimulationTime) {
  AdvanceTo(42);

  const DpiScope* scope = DpiRegisterScope("top.u_plain_time_h_13");
  ASSERT_NE(scope, nullptr);

  s_vpi_time with_scope = {};
  with_scope.type = kSvSimTime;
  EXPECT_EQ(svGetTime(scope, &with_scope), 0);

  s_vpi_time null_scope = {};
  null_scope.type = kSvSimTime;
  EXPECT_EQ(svGetTime(nullptr, &null_scope), 0);

  EXPECT_EQ(with_scope.low, 42u);
  EXPECT_EQ(with_scope.high, null_scope.high);
  EXPECT_EQ(with_scope.low, null_scope.low);
}

TEST_F(SvGetTimeSim, NonNullScopeUnitAndPrecisionMatchNullScope) {
  VpiHandle top = vpi_ctx_.CreateModule("top", "top");
  ASSERT_NE(top, nullptr);
  top->time_precision = -9;

  const DpiScope* scope = DpiRegisterScope("top.u_plain_unit_h_13");
  ASSERT_NE(scope, nullptr);

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

TEST_F(SvGetTimeSim, AScopeWithATimescaleScalesToItsOwnUnit) {
  VpiHandle top = vpi_ctx_.CreateModule("top", "top");
  ASSERT_NE(top, nullptr);
  top->time_precision = -12;
  vpi_ctx_.SetSimTimeUnit(-12);
  AdvanceTo(2500);

  const DpiScope* scope = DpiRegisterScope("top.u_ns_h_13");
  ASSERT_NE(scope, nullptr);
  DpiSetScopeTimescale(scope, -9, -12);

  s_vpi_time scaled = {};
  scaled.type = kSvScaledRealTime;
  EXPECT_EQ(svGetTime(scope, &scaled), 0);
  EXPECT_DOUBLE_EQ(scaled.real, 2.5);

  s_vpi_time sim = {};
  sim.type = kSvScaledRealTime;
  EXPECT_EQ(svGetTime(nullptr, &sim), 0);
  EXPECT_DOUBLE_EQ(sim.real, 2500.0);

  int32_t unit = 0;
  int32_t prec = 0;
  EXPECT_EQ(svGetTimeUnit(scope, &unit), 0);
  EXPECT_EQ(svGetTimePrecision(scope, &prec), 0);
  EXPECT_EQ(unit, -9);
  EXPECT_EQ(prec, -12);
  int32_t sim_unit = 0;
  EXPECT_EQ(svGetTimeUnit(nullptr, &sim_unit), 0);
  EXPECT_EQ(sim_unit, -12);
}

TEST_F(SvGetTimeSim, AScopeWithoutATimescaleReadsAsTheNullScope) {
  vpi_ctx_.SetSimTimeUnit(-12);
  AdvanceTo(7);
  const DpiScope* scope = DpiRegisterScope("top.u_unbound_h_13");
  ASSERT_NE(scope, nullptr);
  const DpiScope* bound = DpiRegisterScope("top.u_bound_h_13");
  DpiSetScopeTimescale(bound, -9, -12);

  s_vpi_time raw = {};
  raw.type = kSvSimTime;
  EXPECT_EQ(svGetTime(bound, &raw), 0);
  EXPECT_EQ(raw.low, 7u);

  s_vpi_time unbound = {};
  unbound.type = kSvScaledRealTime;
  EXPECT_EQ(svGetTime(scope, &unbound), 0);
  EXPECT_DOUBLE_EQ(unbound.real, 7.0);
  int32_t unit = 0;
  int32_t prec = 0;
  EXPECT_FALSE(DpiScopeTimescale(scope, &unit, &prec));
  EXPECT_TRUE(DpiScopeTimescale(bound, &unit, &prec));
  EXPECT_EQ(unit, -9);
  EXPECT_EQ(prec, -12);
}

TEST_F(SvGetTimeSim, NullDestinationReturnsError) {
  AdvanceTo(4);
  EXPECT_EQ(svGetTime(nullptr, nullptr), -1);
  EXPECT_EQ(svGetTimeUnit(nullptr, nullptr), -1);
  EXPECT_EQ(svGetTimePrecision(nullptr, nullptr), -1);
}

}  // namespace
}  // namespace delta
