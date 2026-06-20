#include <gtest/gtest.h>

#include <cstdint>
#include <vector>

#include "common/arena.h"
#include "common/types.h"
#include "helpers_switch_network.h"
#include "simulator/net.h"
#include "simulator/switch_network.h"
#include "simulator/variable.h"

using namespace delta;

namespace {

TEST(BidirectionalSwitchNetwork,
     NetworkResolutionPropagatesAcrossCascadedSwitches) {
  Arena arena;
  auto* va = arena.Create<Variable>();
  va->value = MakeLogic4Vec(arena, 1);
  auto* vb = arena.Create<Variable>();
  vb->value = MakeLogic4Vec(arena, 1);
  auto* vc = arena.Create<Variable>();
  vc->value = MakeLogic4Vec(arena, 1);

  Net a = MakeNet1(arena, va, 1);
  Net b = MakeUndrivenNet(arena, vb);
  Net c = MakeUndrivenNet(arena, vc);

  std::vector<BidirSwitchInst> sw;
  sw.push_back({&a, &b, BidirSwitchKind::kTran, {0, 0}, false});
  sw.push_back({&b, &c, BidirSwitchKind::kTran, {0, 0}, false});
  ResolveBidirSwitchNetwork(sw, arena);

  EXPECT_EQ(ValOf(*vb), kVal1);
  EXPECT_EQ(ValOf(*vc), kVal1);
}

TEST(BidirectionalSwitchNetwork,
     NonConductingSwitchBlocksDownstreamPropagation) {
  Arena arena;
  auto* va = arena.Create<Variable>();
  va->value = MakeLogic4Vec(arena, 1);
  auto* vb = arena.Create<Variable>();
  vb->value = MakeLogic4Vec(arena, 1);
  auto* vc = arena.Create<Variable>();
  vc->value = MakeLogic4Vec(arena, 1);

  Net a = MakeNet1(arena, va, 1);
  Net b = MakeUndrivenNet(arena, vb);
  Net c = MakeUndrivenNet(arena, vc);

  std::vector<BidirSwitchInst> sw;
  sw.push_back({&a, &b, BidirSwitchKind::kTran, {0, 0}, false});
  sw.push_back({&b, &c, BidirSwitchKind::kTranif1, {0, 0}, false});
  ResolveBidirSwitchNetwork(sw, arena);

  EXPECT_EQ(ValOf(*vb), kVal1);
  EXPECT_EQ(ValOf(*vc), kValZ);
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
  sw.push_back({&np.a, &np.b, BidirSwitchKind::kTranif1, {0, 1}, false});
  ResolveBidirSwitchNetwork(sw, np.arena);
  EXPECT_EQ(ValOf(*np.vb), kValX);
}

TEST(BidirectionalSwitchNetwork, BuiltinNetZControlAmbiguousGivesX) {
  auto np = MakeNetPair(0);
  std::vector<BidirSwitchInst> sw;
  sw.push_back({&np.a, &np.b, BidirSwitchKind::kTranif1, {1, 1}, false});
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
  sw.push_back({&np.a, &np.b, BidirSwitchKind::kTranif1, {0, 1}, true});
  ResolveBidirSwitchNetwork(sw, np.arena);
  EXPECT_EQ(ValOf(*np.vb), kValZ);
}

TEST(BidirectionalSwitchNetwork, UserDefinedNetZControlIsOff) {
  auto np = MakeNetPair(1);
  std::vector<BidirSwitchInst> sw;
  sw.push_back({&np.a, &np.b, BidirSwitchKind::kTranif1, {1, 1}, true});
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

}  // namespace
