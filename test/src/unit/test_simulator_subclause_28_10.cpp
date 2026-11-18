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

std::string PullStrengthShown(const std::string& body) {
  std::string src = "module t;\n  wire a, b;\n  ";
  src += body;
  src +=
      "\n  initial #1 $display(\"%v %v\", a, b);\n"
      "endmodule\n";
  SimFixture f;
  return RunCapture(src, f);
}

struct PullStrength {
  const char* body;
  const char* shown;
};

TEST(PullSourceSim, EachStrengthSpecificationSetsTheDrivenStrength) {
  const PullStrength kCases[] = {
      {"pullup (weak1) p1(a);\n  pulldown (weak0) p2(b);", "We1 We0"},
      {"pullup (pull1) p1(a);\n  pulldown (pull0) p2(b);", "Pu1 Pu0"},
      {"pullup (strong1) p1(a);\n  pulldown (strong0) p2(b);", "St1 St0"},
      {"pullup (supply1) p1(a);\n  pulldown (supply0) p2(b);", "Su1 Su0"},
      {"pullup p1(a);\n  pulldown p2(b);", "Pu1 Pu0"},
      {"pullup (strong1) p1(a), p2(b);", "St1 St1"},
      {"pulldown (strong0) p1(a), p2(b);", "St0 St0"},
      {"pullup (weak1, supply0) p1(a);\n  pulldown (weak0, supply1) p2(b);",
       "We1 We0"},
      {"pullup (supply0, weak1) p1(a);\n  pulldown (supply1, weak0) p2(b);",
       "We1 We0"},
      {"pullup (strong1, supply0) p1(a);\n"
       "  pulldown (supply1, strong0) p2(b);",
       "St1 St0"},
      {"pulldown p1(a), p2(b);", "Pu0 Pu0"}};
  for (const auto& c : kCases) {
    std::string shown = c.shown;
    shown += "\n";
    EXPECT_EQ(PullStrengthShown(c.body), shown) << c.body;
  }
}

TEST(PullSourceSim, ABitSelectTerminalPullsOnlyItsBit) {
  EXPECT_EQ(SettleNamedNet("module t;\n  wire [3:0] bus;\n"
                           "  pulldown (bus[2]);\n  pullup (bus[0]);\n"
                           "endmodule\n",
                           "bus"),
            "z0z1");
}

TEST(PullSourceSim, APullSourceInAGenerateBlockDrivesItsNet) {
  SimFixture f;
  auto out = RunCapture(
      "module t;\n"
      "  wire m, n, k;\n"
      "  if (1) begin : gb\n"
      "    pullup (m);\n"
      "  end\n"
      "  for (genvar i = 0; i < 1; i++) begin : lp\n"
      "    pulldown pd(n);\n"
      "  end\n"
      "  case (1)\n"
      "    1: pullup (strong1) pk(k);\n"
      "  endcase\n"
      "  initial #1 $display(\"%v %v %v\", m, n, k);\n"
      "endmodule\n",
      f);
  EXPECT_EQ(out, "Pu1 Pu0 St1\n");
}

}  // namespace
