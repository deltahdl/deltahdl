#pragma once

#include <gtest/gtest.h>

#include <cstdint>

#include "fixture_simulator.h"
#include "simulator/lowerer.h"
#include "simulator/scheduler.h"
#include "simulator/sim_context.h"
#include "simulator/variable.h"

using namespace delta;

// Elaborates, lowers and runs a "zero-delay routes to (re)inactive" scenario
// whose source declares logic [7:0] b, snap, done and ends with:
//   b <= <expected_b>;  done = #0 8'd1;  snap = b;
// After the run, `done` must have updated to 1, `snap` must still observe the
// pre-NBA value of b (0), and b must have taken its nonblocking update.
inline void RunZeroDelayRouteScenario(SimFixture& f, const char* src,
                                      uint64_t expected_b) {
  auto* design = ElaborateSrc(src, f);
  ASSERT_NE(design, nullptr);
  Lowerer lowerer(f.ctx, f.arena, f.diag);
  lowerer.Lower(design);
  f.scheduler.Run();
  EXPECT_EQ(f.ctx.FindVariable("done")->value.ToUint64(), 1u);
  EXPECT_EQ(f.ctx.FindVariable("snap")->value.ToUint64(), 0u);
  EXPECT_EQ(f.ctx.FindVariable("b")->value.ToUint64(), expected_b);
}
