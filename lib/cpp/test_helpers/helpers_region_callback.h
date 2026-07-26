#pragma once

#include <gtest/gtest.h>

#include <cstdint>
#include <string>
#include <string_view>

#include "fixture_simulator.h"
#include "simulator/lowerer.h"
#include "simulator/scheduler.h"
#include "simulator/variable.h"

using namespace delta;

// Lowers `src`, schedules a callback into `region` at time 0 that reads the
// variable `var_name`, runs the design, and checks the callback ran and read
// `expected`.
//
// A rule that says which values a callback in some region observes is stated
// by putting a callback there and letting a real design settle the value it
// reads: what the callback sees is the verdict on whether the regions the
// value passes through were drained first. A callback that never ran would
// leave its sample at its initial value, so the run is checked as well.
inline void ExpectRegionCallbackReads(SimFixture& f, const char* src,
                                      Region region, std::string_view var_name,
                                      uint64_t expected) {
  auto* design = ElaborateSrc(src, f);
  ASSERT_FALSE(f.has_errors);

  Lowerer lowerer(f.ctx, f.arena, f.diag);
  lowerer.Lower(design);

  bool ran = false;
  uint64_t sample = 0;
  auto* ev = f.scheduler.GetEventPool().Acquire();
  ev->callback = [&]() {
    ran = true;
    sample = f.ctx.FindVariable(var_name)->value.ToUint64();
  };
  f.scheduler.ScheduleEvent({0}, region, ev);

  f.scheduler.Run();
  EXPECT_TRUE(ran);
  EXPECT_EQ(sample, expected);
}
