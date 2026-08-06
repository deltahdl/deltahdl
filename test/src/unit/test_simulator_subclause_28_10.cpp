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

// Same real elaborate/lower/run pipeline as SettleNetY, but takes a full module
// `src` and reports the settled value of the named `net`. Used where the net is
// a vector or where several nets are driven, so the declaration cannot be the
// fixed scalar `wire y`.
std::string SettleNamedNet(const std::string& src, const char* net) {
  SimFixture f;
  auto* design = ElaborateSrc(src, f);
  EXPECT_NE(design, nullptr);
  if (!design) return "<elaborate-failed>";
  Lowerer lowerer(f.ctx, f.arena, f.diag);
  lowerer.Lower(design);
  f.scheduler.Run();
  auto* var = f.ctx.FindVariable(net);
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

// §28.10: a strength0 on a pullup is ignored — a pullup only ever drives 1, and
// the paired form's strength0 must not govern that drive. Here the pullup
// drives 1 at the operative weak1 while carrying a supply0 that must be
// discarded; the competing strong 0 outranks weak, so the net settles to 0.
// Were the ignored supply0 instead applied to the pullup's drive, it would
// outrank the strong 0 and force the net to 1 — so observing 0 confirms the
// supply0 was dropped and weak1 alone governed.
TEST(PullSourceSim, PullupIgnoresOppositeStrengthAtRuntime) {
  EXPECT_EQ(SettleNetY("pullup (supply0, weak1) p(y);\n  assign y = 1'b0;"),
            "0");
}

// §28.10, symmetric: a strength1 on a pulldown is ignored. The pulldown drives
// 0 at the operative weak0 alongside a supply1 that must be discarded; the
// strong 1 outranks weak, so the net settles to 1. A leaked supply1 would
// outrank the strong 1 and force 0, so observing 1 confirms the supply1 was
// ignored.
TEST(PullSourceSim, PulldownIgnoresOppositeStrengthAtRuntime) {
  EXPECT_EQ(SettleNetY("pulldown (weak0, supply1) p(y);\n  assign y = 1'b1;"),
            "1");
}

// §28.10 places its logic value on the nets in the terminal list — end-to-end
// over the §28.3.6 instance-array form: an array of pullups sized to a 4-bit
// vector distributes one element to each bit, so every bit is pulled high and
// the whole bus settles to all ones. Built from real array source syntax and
// run through the pipeline, this observes the value rule applied per array
// element.
TEST(PullSourceSim, PullupInstanceArrayPullsEveryBitHigh) {
  EXPECT_EQ(
      SettleNamedNet(
          "module t;\n  wire [3:0] bus;\n  pullup pu[3:0](bus);\nendmodule\n",
          "bus"),
      "1111");
}

// §28.10, symmetric §28.3.6 instance-array end-to-end: a pulldown array places
// 0 on each bit of the vector, so the bus settles to all zeros.
TEST(PullSourceSim, PulldownInstanceArrayPullsEveryBitLow) {
  EXPECT_EQ(SettleNamedNet("module t;\n  wire [3:0] bus;\n  pulldown "
                           "pd[3:0](bus);\nendmodule\n",
                           "bus"),
            "0000");
}

// §28.10's value goes on "the nets connected in its terminal list" — the source
// clause illustrates this with two comma-separated named instances, each
// driving its own net. End-to-end: both nets independently settle to 1,
// confirming the value is placed on every listed instance's terminal.
TEST(PullSourceSim, PullupCommaListPlacesValueOnEachNet) {
  const char* src =
      "module t;\n  wire a, b;\n  pullup g1(a), g2(b);\nendmodule\n";
  EXPECT_EQ(SettleNamedNet(src, "a"), "1");
  EXPECT_EQ(SettleNamedNet(src, "b"), "1");
}

}  // namespace
