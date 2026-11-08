#include <gtest/gtest.h>

#include <string>

#include "fixture_simulator.h"
#include "simulator/lowerer.h"
#include "simulator/variable.h"

using namespace delta;

namespace {

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

TEST(PullSourceSim, PullupDrivesNetHigh) {
  EXPECT_EQ(SettleNetY("pullup p(y);"), "1");
}

TEST(PullSourceSim, PulldownDrivesNetLow) {
  EXPECT_EQ(SettleNetY("pulldown p(y);"), "0");
}

TEST(PullSourceSim, PullupDefaultPullYieldsToStrongDriver) {
  EXPECT_EQ(SettleNetY("pullup p(y);\n  assign y = 1'b0;"), "0");
}

TEST(PullSourceSim, PulldownDefaultPullYieldsToStrongDriver) {
  EXPECT_EQ(SettleNetY("pulldown p(y);\n  assign y = 1'b1;"), "1");
}

TEST(PullSourceSim, PullupExplicitSupplyOverridesStrongDriver) {
  EXPECT_EQ(SettleNetY("pullup (supply1) p(y);\n  assign y = 1'b0;"), "1");
}

TEST(PullSourceSim, PulldownExplicitSupplyOverridesStrongDriver) {
  EXPECT_EQ(SettleNetY("pulldown (supply0) p(y);\n  assign y = 1'b1;"), "0");
}

TEST(PullSourceSim, PullupIgnoresOppositeStrengthAtRuntime) {
  EXPECT_EQ(SettleNetY("pullup (supply0, weak1) p(y);\n  assign y = 1'b0;"),
            "0");
}

TEST(PullSourceSim, PulldownIgnoresOppositeStrengthAtRuntime) {
  EXPECT_EQ(SettleNetY("pulldown (weak0, supply1) p(y);\n  assign y = 1'b1;"),
            "1");
}

TEST(PullSourceSim, PullupInstanceArrayPullsEveryBitHigh) {
  EXPECT_EQ(
      SettleNamedNet(
          "module t;\n  wire [3:0] bus;\n  pullup pu[3:0](bus);\nendmodule\n",
          "bus"),
      "1111");
}

TEST(PullSourceSim, PulldownInstanceArrayPullsEveryBitLow) {
  EXPECT_EQ(SettleNamedNet("module t;\n  wire [3:0] bus;\n  pulldown "
                           "pd[3:0](bus);\nendmodule\n",
                           "bus"),
            "0000");
}

TEST(PullSourceSim, PullupCommaListPlacesValueOnEachNet) {
  const char* src =
      "module t;\n  wire a, b;\n  pullup g1(a), g2(b);\nendmodule\n";
  EXPECT_EQ(SettleNamedNet(src, "a"), "1");
  EXPECT_EQ(SettleNamedNet(src, "b"), "1");
}

}  // namespace
