#pragma once

#include <gtest/gtest.h>

#include "fixture_simulator.h"
#include "simulator/lowerer.h"
#include "simulator/variable.h"

using namespace delta;

// The observation that a nonblocking assignment evaluates in two steps: every
// right-hand side in the time step is sampled before any left-hand side is
// updated.
//
// Two nonblocking assignments issued together, each reading the other's
// variable, therefore exchange values. A sequential read-after-write -- what a
// blocking assignment would do, and what an implementation that applied each
// update as it went would produce -- leaves both variables holding the first
// source's value instead, so a genuine swap rules that misreading out.
//
// The fixture is caller-owned, so what the run left in its context stays
// readable afterwards.
inline void ExpectNonblockingPairExchangesValues(SimFixture& f) {
  auto* design = ElaborateSrc(
      "module t;\n"
      "  logic [7:0] a, b;\n"
      "  initial begin\n"
      "    a = 8'd10;\n"
      "    b = 8'd20;\n"
      "    a <= b;\n"
      "    b <= a;\n"
      "  end\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  Lowerer lowerer(f.ctx, f.arena, f.diag);
  lowerer.Lower(design);
  f.scheduler.Run();
  EXPECT_EQ(f.ctx.FindVariable("a")->value.ToUint64(), 20u);
  EXPECT_EQ(f.ctx.FindVariable("b")->value.ToUint64(), 10u);
}
