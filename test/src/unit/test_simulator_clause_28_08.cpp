#include <gtest/gtest.h>

#include "helpers_switch_network.h"
#include "model_switch_eval.h"
#include "simulator/scheduler.h"

namespace {

TEST(SwitchProcessingSchedulingSim, TransistorSourceElements) {
  Arena arena;
  Scheduler sched(arena);

  enum class TranType : std::uint8_t {
    kTran,
    kTranif0,
    kTranif1,
    kRtran,
    kRtranif0,
    kRtranif1
  };
  std::vector<TranType> transistors = {
      TranType::kTran,  TranType::kTranif0,  TranType::kTranif1,
      TranType::kRtran, TranType::kRtranif0, TranType::kRtranif1};

  int resolved_count = 0;

  auto* eval = sched.GetEventPool().Acquire();
  eval->kind = EventKind::kEvaluation;
  eval->callback = [&]() {
    for (auto type : transistors) {
      (void)type;
      auto* update = sched.GetEventPool().Acquire();
      update->kind = EventKind::kUpdate;
      update->callback = [&]() { ++resolved_count; };
      sched.ScheduleEvent(sched.CurrentTime(), Region::kActive, update);
    }
  };
  sched.ScheduleEvent({0}, Region::kActive, eval);

  sched.Run();

  EXPECT_EQ(resolved_count, 6);
}

TEST(SwitchProcessing, TranPropagatesDrivenToUndriven) {
  auto np = MakeNetPair(1);
  std::vector<SwitchInst> sw;
  sw.push_back({&np.a, &np.b, SwitchKind::kTran, {}, false});
  ResolveSwitchNetwork(sw, np.arena);
  EXPECT_EQ(ValOf(*np.vb), kVal1);
}

TEST(SwitchProcessing, TranBidirectionalPropagation) {
  Arena arena;
  auto* va = arena.Create<Variable>();
  va->value = MakeLogic4Vec(arena, 1);
  auto* vb = arena.Create<Variable>();
  vb->value = MakeLogic4Vec(arena, 1);

  Net a = MakeUndrivenNet(arena, va);
  Net b = MakeNet1(arena, vb, 0);

  std::vector<SwitchInst> sw;
  sw.push_back({&a, &b, SwitchKind::kTran, {}, false});
  ResolveSwitchNetwork(sw, arena);
  EXPECT_EQ(ValOf(*va), kVal0);
}

TEST(SwitchProcessing, Tranif1ConductsWhenControlHigh) {
  auto np = MakeNetPair(1);
  std::vector<SwitchInst> sw;
  sw.push_back({&np.a, &np.b, SwitchKind::kTranif1, {1, 0}, false});
  ResolveSwitchNetwork(sw, np.arena);
  EXPECT_EQ(ValOf(*np.vb), kVal1);
}

TEST(SwitchProcessing, Tranif1BlocksWhenControlLow) {
  auto np = MakeNetPair(1);
  std::vector<SwitchInst> sw;
  sw.push_back({&np.a, &np.b, SwitchKind::kTranif1, {0, 0}, false});
  ResolveSwitchNetwork(sw, np.arena);
  EXPECT_EQ(ValOf(*np.vb), kValZ);
}

TEST(SwitchProcessing, Tranif0ConductsWhenControlLow) {
  auto np = MakeNetPair(1);
  std::vector<SwitchInst> sw;
  sw.push_back({&np.a, &np.b, SwitchKind::kTranif0, {0, 0}, false});
  ResolveSwitchNetwork(sw, np.arena);
  EXPECT_EQ(ValOf(*np.vb), kVal1);
}

TEST(SwitchProcessing, Tranif0BlocksWhenControlHigh) {
  auto np = MakeNetPair(1);
  std::vector<SwitchInst> sw;
  sw.push_back({&np.a, &np.b, SwitchKind::kTranif0, {1, 0}, false});
  ResolveSwitchNetwork(sw, np.arena);
  EXPECT_EQ(ValOf(*np.vb), kValZ);
}

TEST(SwitchProcessing, RtranBidirectionalPropagation) {
  Arena arena;
  auto* va = arena.Create<Variable>();
  va->value = MakeLogic4Vec(arena, 1);
  auto* vb = arena.Create<Variable>();
  vb->value = MakeLogic4Vec(arena, 1);

  Net a = MakeUndrivenNet(arena, va);
  Net b = MakeNet1(arena, vb, 0);

  std::vector<SwitchInst> sw;
  sw.push_back({&a, &b, SwitchKind::kRtran, {}, false});
  ResolveSwitchNetwork(sw, arena);
  EXPECT_EQ(ValOf(*va), kVal0);
}

TEST(SwitchProcessing, RtranPropagatesDrivenToUndriven) {
  auto np = MakeNetPair(1);
  std::vector<SwitchInst> sw;
  sw.push_back({&np.a, &np.b, SwitchKind::kRtran, {}, false});
  ResolveSwitchNetwork(sw, np.arena);
  EXPECT_EQ(ValOf(*np.vb), kVal1);
}

TEST(SwitchProcessing, Rtranif1ConductsWhenControlHigh) {
  auto np = MakeNetPair(1);
  std::vector<SwitchInst> sw;
  sw.push_back({&np.a, &np.b, SwitchKind::kRtranif1, {1, 0}, false});
  ResolveSwitchNetwork(sw, np.arena);
  EXPECT_EQ(ValOf(*np.vb), kVal1);
}

TEST(SwitchProcessing, Rtranif1BlocksWhenControlLow) {
  auto np = MakeNetPair(1);
  std::vector<SwitchInst> sw;
  sw.push_back({&np.a, &np.b, SwitchKind::kRtranif1, {0, 0}, false});
  ResolveSwitchNetwork(sw, np.arena);
  EXPECT_EQ(ValOf(*np.vb), kValZ);
}

TEST(SwitchProcessing, Rtranif0ConductsWhenControlLow) {
  auto np = MakeNetPair(1);
  std::vector<SwitchInst> sw;
  sw.push_back({&np.a, &np.b, SwitchKind::kRtranif0, {0, 0}, false});
  ResolveSwitchNetwork(sw, np.arena);
  EXPECT_EQ(ValOf(*np.vb), kVal1);
}

TEST(SwitchProcessing, Rtranif0BlocksWhenControlHigh) {
  auto np = MakeNetPair(1);
  std::vector<SwitchInst> sw;
  sw.push_back({&np.a, &np.b, SwitchKind::kRtranif0, {1, 0}, false});
  ResolveSwitchNetwork(sw, np.arena);
  EXPECT_EQ(ValOf(*np.vb), kValZ);
}

TEST(SwitchProcessing, Tranif1PropagatesReverseDirection) {
  Arena arena;
  auto* va = arena.Create<Variable>();
  va->value = MakeLogic4Vec(arena, 1);
  auto* vb = arena.Create<Variable>();
  vb->value = MakeLogic4Vec(arena, 1);
  Net a = MakeUndrivenNet(arena, va);
  Net b = MakeNet1(arena, vb, 0);
  std::vector<SwitchInst> sw;
  sw.push_back({&a, &b, SwitchKind::kTranif1, {1, 0}, false});
  ResolveSwitchNetwork(sw, arena);
  EXPECT_EQ(ValOf(*va), kVal0);
}

TEST(SwitchProcessing, Rtranif0PropagatesReverseDirection) {
  Arena arena;
  auto* va = arena.Create<Variable>();
  va->value = MakeLogic4Vec(arena, 1);
  auto* vb = arena.Create<Variable>();
  vb->value = MakeLogic4Vec(arena, 1);
  Net a = MakeUndrivenNet(arena, va);
  Net b = MakeNet1(arena, vb, 0);
  std::vector<SwitchInst> sw;
  sw.push_back({&a, &b, SwitchKind::kRtranif0, {0, 0}, false});
  ResolveSwitchNetwork(sw, arena);
  EXPECT_EQ(ValOf(*va), kVal0);
}

// §28.8 control-input delay rules, observed on the production helpers in
// src/simulator/switch_network.cpp.
TEST(BidirSwitchControlDelay, TwoDelaysFirstIsTurnOn) {
  BidirSwitchDelaySpec spec{true, true, 10, 20};
  EXPECT_EQ(BidirSwitchTurnOnDelay(spec), 10u);
}

TEST(BidirSwitchControlDelay, TwoDelaysSecondIsTurnOff) {
  BidirSwitchDelaySpec spec{true, true, 10, 20};
  EXPECT_EQ(BidirSwitchTurnOffDelay(spec), 20u);
}

TEST(BidirSwitchControlDelay, OneDelayAppliesToBothEdges) {
  BidirSwitchDelaySpec spec{true, false, 7, 0};
  EXPECT_EQ(BidirSwitchTurnOnDelay(spec), 7u);
  EXPECT_EQ(BidirSwitchTurnOffDelay(spec), 7u);
}

TEST(BidirSwitchControlDelay, NoDelayMeansNoControlDelay) {
  BidirSwitchDelaySpec spec{};
  EXPECT_EQ(BidirSwitchTurnOnDelay(spec), 0u);
  EXPECT_EQ(BidirSwitchTurnOffDelay(spec), 0u);
  EXPECT_EQ(BidirSwitchBuiltinControlXZDelay(spec), 0u);
}

TEST(BidirSwitchControlDelay, BuiltinXZTakesSmallerOfTwoDelays) {
  EXPECT_EQ(BidirSwitchBuiltinControlXZDelay({true, true, 10, 20}), 10u);
  EXPECT_EQ(BidirSwitchBuiltinControlXZDelay({true, true, 20, 10}), 10u);
}

TEST(BidirSwitchControlDelay, BuiltinXZWithOneDelayUsesIt) {
  EXPECT_EQ(BidirSwitchBuiltinControlXZDelay({true, false, 5, 0}), 5u);
}

// §28.8: for bidirectional switches connecting built-in net types, the
// nonresistive tran/tranif0/tranif1 devices alter strength in only one case
// (§28.13) -- a supply strength crossing the switch is reduced to strong. This
// grounds the contrast with the user-defined-net rule below.
TEST(BidirSwitchStrength, BuiltinTranReducesSupplyToStrong) {
  auto np = MakeNetPair(1);
  np.a.resolved_strength = {Strength::kSupply, Strength::kSupply,
                            Strength::kSupply, Strength::kSupply};
  std::vector<SwitchInst> sw;
  sw.push_back({&np.a, &np.b, SwitchKind::kTran, {0, 0}, false});
  ResolveSwitchNetwork(sw, np.arena);
  EXPECT_EQ(np.b.resolved_strength.s1_hi, Strength::kStrong);
  EXPECT_EQ(np.b.resolved_strength.s1_lo, Strength::kStrong);
}

// §28.8: there shall be no strength reduction in bidirectional switches
// connecting user-defined net types, so the same supply-strength source crosses
// a user-defined-net tran with its strength intact rather than reduced.
TEST(BidirSwitchStrength, UserDefinedNetSwitchDoesNotReduceStrength) {
  auto np = MakeNetPair(1);
  np.a.resolved_strength = {Strength::kSupply, Strength::kSupply,
                            Strength::kSupply, Strength::kSupply};
  std::vector<SwitchInst> sw;
  sw.push_back({&np.a, &np.b, SwitchKind::kTran, {0, 0}, true});
  ResolveSwitchNetwork(sw, np.arena);
  EXPECT_EQ(np.b.resolved_strength.s1_hi, Strength::kSupply);
  EXPECT_EQ(np.b.resolved_strength.s1_lo, Strength::kSupply);
}

TEST(SwitchProcessing, BidirectionalPropagationIgnoresControlDelaySpec) {
  auto np = MakeNetPair(1);
  std::vector<SwitchInst> sw;
  sw.push_back({&np.a,
                &np.b,
                SwitchKind::kTranif1,
                {1, 0},
                false,
                PassSwitchDelaySpec{true, true, 100, 200}});
  ResolveSwitchNetwork(sw, np.arena);
  EXPECT_EQ(ValOf(*np.vb), kVal1);
}

}  // namespace
