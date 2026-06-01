#include <gtest/gtest.h>

#include <string>

#include "fixture_simulator.h"
#include "simulator/lowerer.h"
#include "simulator/variable.h"

using namespace delta;

namespace {

// Elaborates, lowers, and runs `src`, then returns the settled 4-state value of
// net `y` ("0", "1", "x", or "z"). This exercises the real production path: the
// elaborator lowering of a pullup/pulldown source to a strength-bearing
// continuous assignment, plus the simulator's net resolution of the resulting
// driver(s) — not a reference model.
std::string SettleNetY(const std::string& body) {
  SimFixture f;
  std::string src = "module t;\n  wire y;\n  " + body + "\nendmodule\n";
  auto* design = ElaborateSrc(src, f);
  EXPECT_NE(design, nullptr);
  if (!design) return "<elaborate-failed>";
  Lowerer lowerer(f.ctx, f.arena, f.diag);
  lowerer.Lower(design);
  f.scheduler.Run();
  auto* var = f.ctx.FindVariable("y");
  EXPECT_NE(var, nullptr);
  return var ? var->value.ToString() : "<no-output>";
}

// §28.10: a pullup source places logic 1 on its net. With no competing driver,
// the resolved value is simply 1.
TEST(PullSourceSim, PullupDrivesNetHigh) {
  EXPECT_EQ(SettleNetY("pullup p(y);"), "1");
}

// §28.10: a pulldown source places logic 0 on its net.
TEST(PullSourceSim, PulldownDrivesNetLow) {
  EXPECT_EQ(SettleNetY("pulldown p(y);"), "0");
}

// §28.10: absent an explicit specification, the placed signal carries pull
// strength. Pull is weaker than the strong strength of a plain continuous
// assignment, so the strong 0 wins the resolution — observing that production
// gave the pullup pull (not strong/supply) strength.
TEST(PullSourceSim, PullupDefaultPullYieldsToStrongDriver) {
  EXPECT_EQ(SettleNetY("pullup p(y);\n  assign y = 1'b0;"), "0");
}

// Symmetric check for a pulldown: its default pull-strength 0 loses to a strong
// driver placing 1.
TEST(PullSourceSim, PulldownDefaultPullYieldsToStrongDriver) {
  EXPECT_EQ(SettleNetY("pulldown p(y);\n  assign y = 1'b1;"), "1");
}

// §28.10: an explicit strength1 on a pullup is honored. supply1 outranks the
// strong 0 of the plain assignment, so the pullup now wins — distinguishing the
// honored explicit strength from the default pull, which lost above.
TEST(PullSourceSim, PullupExplicitSupplyOverridesStrongDriver) {
  EXPECT_EQ(SettleNetY("pullup (supply1) p(y);\n  assign y = 1'b0;"), "1");
}

// §28.10: an explicit strength0 on a pulldown is honored. supply0 outranks the
// strong 1 of the plain assignment, so the pulldown wins.
TEST(PullSourceSim, PulldownExplicitSupplyOverridesStrongDriver) {
  EXPECT_EQ(SettleNetY("pulldown (supply0) p(y);\n  assign y = 1'b1;"), "0");
}

}  // namespace
