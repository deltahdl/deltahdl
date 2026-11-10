#include <gtest/gtest.h>

#include <string>
#include <vector>

#include "common/arena.h"
#include "common/types.h"
#include "fixture_simulator.h"
#include "helpers_switch_network.h"
#include "simulator/net.h"
#include "simulator/switch_network.h"
#include "simulator/variable.h"

using namespace delta;

namespace {

struct CascadeVars {
  Arena arena;
  Variable* va = nullptr;
  Variable* vb = nullptr;
  Variable* vc = nullptr;
};

static CascadeVars ResolveCascade(BidirSwitchKind second_kind) {
  CascadeVars cv;
  cv.va = cv.arena.Create<Variable>();
  cv.va->value = MakeLogic4Vec(cv.arena, 1);
  cv.vb = cv.arena.Create<Variable>();
  cv.vb->value = MakeLogic4Vec(cv.arena, 1);
  cv.vc = cv.arena.Create<Variable>();
  cv.vc->value = MakeLogic4Vec(cv.arena, 1);

  Net a = MakeNet1(cv.arena, cv.va, 1);
  Net b = MakeUndrivenNet(cv.arena, cv.vb);
  Net c = MakeUndrivenNet(cv.arena, cv.vc);

  std::vector<BidirSwitchInst> sw;
  sw.push_back({&a, &b, BidirSwitchKind::kTran, {0, 0}, false});
  sw.push_back({&b, &c, second_kind, {0, 0}, false});
  ResolveBidirSwitchNetwork(sw, cv.arena);
  return cv;
}

TEST(BidirectionalSwitchNetwork,
     NetworkResolutionPropagatesAcrossCascadedSwitches) {
  CascadeVars cv = ResolveCascade(BidirSwitchKind::kTran);
  EXPECT_EQ(ValOf(*cv.vb), kVal1);
  EXPECT_EQ(ValOf(*cv.vc), kVal1);
}

TEST(BidirectionalSwitchNetwork,
     NonConductingSwitchBlocksDownstreamPropagation) {
  CascadeVars cv = ResolveCascade(BidirSwitchKind::kTranif1);
  EXPECT_EQ(ValOf(*cv.vb), kVal1);
  EXPECT_EQ(ValOf(*cv.vc), kValZ);
}

TEST(BidirectionalSwitchNetwork, AllSixSourceElementsAreBidirectional) {
  for (auto kind : {BidirSwitchKind::kTran, BidirSwitchKind::kRtran,
                    BidirSwitchKind::kTranif0, BidirSwitchKind::kTranif1,
                    BidirSwitchKind::kRtranif0, BidirSwitchKind::kRtranif1}) {
    auto np = MakeNetPair(1);
    Logic4Word ctrl = (kind == BidirSwitchKind::kTranif0 ||
                       kind == BidirSwitchKind::kRtranif0)
                          ? Logic4Word{0, 0}
                          : Logic4Word{1, 0};
    std::vector<BidirSwitchInst> sw;
    sw.push_back({&np.a, &np.b, kind, ctrl, false});
    ResolveBidirSwitchNetwork(sw, np.arena);
    EXPECT_EQ(ValOf(*np.vb), kVal1);
  }
}

TEST(BidirectionalSwitchNetwork, BuiltinNetXControlAmbiguousGivesX) {
  auto np = MakeNetPair(1);
  std::vector<BidirSwitchInst> sw;
  sw.push_back({&np.a, &np.b, BidirSwitchKind::kTranif1, {1, 1}, false});
  ResolveBidirSwitchNetwork(sw, np.arena);
  EXPECT_EQ(ValOf(*np.vb), kValX);
}

TEST(BidirectionalSwitchNetwork, BuiltinNetZControlAmbiguousGivesX) {
  auto np = MakeNetPair(0);
  std::vector<BidirSwitchInst> sw;
  sw.push_back({&np.a, &np.b, BidirSwitchKind::kTranif1, {0, 1}, false});
  ResolveBidirSwitchNetwork(sw, np.arena);
  EXPECT_EQ(ValOf(*np.vb), kValX);
}

TEST(BidirectionalSwitchNetwork,
     BuiltinNetUnknownControlUniqueLogicLevelIsPreserved) {
  Arena arena;
  auto* va = arena.Create<Variable>();
  va->value = MakeLogic4Vec(arena, 1);
  auto* vb = arena.Create<Variable>();
  vb->value = MakeLogic4Vec(arena, 1);

  Net a = MakeNet1(arena, va, 1);
  Net b = MakeNet1(arena, vb, 1);

  std::vector<BidirSwitchInst> sw;
  sw.push_back({&a, &b, BidirSwitchKind::kTranif1, {0, 1}, false});
  ResolveBidirSwitchNetwork(sw, arena);

  EXPECT_EQ(ValOf(*va), kVal1);
  EXPECT_EQ(ValOf(*vb), kVal1);
}

TEST(BidirectionalSwitchNetwork,
     UserDefinedNetKnownControlOnResolvesAsSingleNet) {
  auto np = MakeNetPair(1);
  std::vector<BidirSwitchInst> sw;
  sw.push_back({&np.a, &np.b, BidirSwitchKind::kTranif1, {1, 0}, true});
  ResolveBidirSwitchNetwork(sw, np.arena);
  EXPECT_EQ(ValOf(*np.vb), kVal1);
}

TEST(BidirectionalSwitchNetwork,
     UserDefinedNetKnownControlOffResolvesSeparately) {
  auto np = MakeNetPair(1);
  std::vector<BidirSwitchInst> sw;
  sw.push_back({&np.a, &np.b, BidirSwitchKind::kTranif1, {0, 0}, true});
  ResolveBidirSwitchNetwork(sw, np.arena);
  EXPECT_EQ(ValOf(*np.vb), kValZ);
}

TEST(BidirectionalSwitchNetwork, UserDefinedNetXControlIsOff) {
  auto np = MakeNetPair(1);
  std::vector<BidirSwitchInst> sw;
  sw.push_back({&np.a, &np.b, BidirSwitchKind::kTranif1, {1, 1}, true});
  ResolveBidirSwitchNetwork(sw, np.arena);
  EXPECT_EQ(ValOf(*np.vb), kValZ);
}

TEST(BidirectionalSwitchNetwork, UserDefinedNetZControlIsOff) {
  auto np = MakeNetPair(1);
  std::vector<BidirSwitchInst> sw;
  sw.push_back({&np.a, &np.b, BidirSwitchKind::kTranif1, {0, 1}, true});
  ResolveBidirSwitchNetwork(sw, np.arena);
  EXPECT_EQ(ValOf(*np.vb), kValZ);
}

TEST(BidirectionalSwitchNetwork, ConductsAlwaysForTranAndRtranIgnoringControl) {
  EXPECT_TRUE(BidirSwitchConducts(BidirSwitchKind::kTran, {0, 0}));
  EXPECT_TRUE(BidirSwitchConducts(BidirSwitchKind::kTran, {1, 0}));
  EXPECT_TRUE(BidirSwitchConducts(BidirSwitchKind::kTran, {0, 1}));
  EXPECT_TRUE(BidirSwitchConducts(BidirSwitchKind::kTran, {1, 1}));
  EXPECT_TRUE(BidirSwitchConducts(BidirSwitchKind::kRtran, {0, 1}));
  EXPECT_TRUE(BidirSwitchConducts(BidirSwitchKind::kRtran, {1, 1}));
}

TEST(BidirectionalSwitchNetwork,
     ControlIsUnknownDistinguishesIfVariantsFromTran) {
  EXPECT_FALSE(BidirSwitchControlIsUnknown(BidirSwitchKind::kTran, {0, 1}));
  EXPECT_FALSE(BidirSwitchControlIsUnknown(BidirSwitchKind::kRtran, {1, 1}));
  EXPECT_FALSE(BidirSwitchControlIsUnknown(BidirSwitchKind::kTranif1, {0, 0}));
  EXPECT_FALSE(BidirSwitchControlIsUnknown(BidirSwitchKind::kTranif1, {1, 0}));
  EXPECT_TRUE(BidirSwitchControlIsUnknown(BidirSwitchKind::kTranif1, {0, 1}));
  EXPECT_TRUE(BidirSwitchControlIsUnknown(BidirSwitchKind::kTranif1, {1, 1}));
  EXPECT_TRUE(BidirSwitchControlIsUnknown(BidirSwitchKind::kTranif0, {0, 1}));
  EXPECT_TRUE(BidirSwitchControlIsUnknown(BidirSwitchKind::kRtranif1, {1, 1}));
}

std::string RunSwitch(const std::string& net_decl, const std::string& kind,
                      const std::string& control) {
  SimFixture f;
  return RunCapture("module top;\n" + net_decl + "  logic c = 1'b" + control +
                        ";\n"
                        "  assign a = 1'b1;\n"
                        "  " +
                        kind +
                        " t (a, b, c);\n"
                        "  initial #1 $display(\"a=%b b=%b\", a, b);\n"
                        "endmodule\n",
                    f);
}

TEST(BidirectionalSwitchNetwork, BuiltinNetSwitchWithUnknownControlGivesX) {
  for (const char* kind : {"tranif1", "tranif0", "rtranif1", "rtranif0"}) {
    for (const char* control : {"x", "z"}) {
      EXPECT_EQ(RunSwitch("  wire a, b;\n", kind, control), "a=1 b=x\n")
          << kind << " " << control;
    }
  }
}

constexpr const char* kOredNets =
    "  function automatic logic ored(input logic d[]);\n"
    "    ored = 1'b0;\n"
    "    foreach (d[i]) ored |= d[i];\n"
    "  endfunction\n"
    "  nettype logic ored_t with ored;\n"
    "  ored_t a, b;\n"
    "  assign b = 1'b0;\n";

TEST(BidirectionalSwitchNetwork, UserDefinedNetSwitchWithUnknownControlIsOff) {
  for (const char* kind : {"tranif1", "tranif0"}) {
    for (const char* control : {"x", "z"}) {
      EXPECT_EQ(RunSwitch(kOredNets, kind, control), "a=1 b=0\n")
          << kind << " " << control;
    }
  }
}

TEST(BidirectionalSwitchNetwork, UserDefinedNetSwitchWithKnownControlConducts) {
  EXPECT_EQ(RunSwitch(kOredNets, "tranif1", "1"), "a=1 b=1\n");
  EXPECT_EQ(RunSwitch(kOredNets, "tranif0", "0"), "a=1 b=1\n");
  EXPECT_EQ(RunSwitch(kOredNets, "tranif1", "0"), "a=1 b=0\n");
  EXPECT_EQ(RunSwitch(kOredNets, "tranif0", "1"), "a=1 b=0\n");
}

}  // namespace
