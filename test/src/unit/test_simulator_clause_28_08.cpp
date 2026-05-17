#include <gtest/gtest.h>

#include "helpers_switch_network.h"
#include "model_switch_eval.h"
#include "simulator/scheduler.h"

namespace {

TEST(BidirectionalSwitches, AllKindsAreBidirectional) {
  EXPECT_TRUE(IsBidirectional(SwitchType::kTran));
  EXPECT_TRUE(IsBidirectional(SwitchType::kRtran));
  EXPECT_TRUE(IsBidirectional(SwitchType::kTranif0));
  EXPECT_TRUE(IsBidirectional(SwitchType::kTranif1));
  EXPECT_TRUE(IsBidirectional(SwitchType::kRtranif0));
  EXPECT_TRUE(IsBidirectional(SwitchType::kRtranif1));
}

TEST(BidirectionalSwitches, TranNoDelays) {
  EXPECT_FALSE(AcceptsDelaySpec(SwitchType::kTran));
  EXPECT_FALSE(AcceptsDelaySpec(SwitchType::kRtran));
}

TEST(BidirectionalSwitches, PassEnableKindsAcceptUpToTwoDelays) {
  EXPECT_TRUE(AcceptsDelaySpec(SwitchType::kTranif0));
  EXPECT_TRUE(AcceptsDelaySpec(SwitchType::kTranif1));
  EXPECT_TRUE(AcceptsDelaySpec(SwitchType::kRtranif0));
  EXPECT_TRUE(AcceptsDelaySpec(SwitchType::kRtranif1));
  EXPECT_EQ(MaxSwitchDelays(SwitchType::kTranif0), 2u);
  EXPECT_EQ(MaxSwitchDelays(SwitchType::kTranif1), 2u);
  EXPECT_EQ(MaxSwitchDelays(SwitchType::kRtranif0), 2u);
  EXPECT_EQ(MaxSwitchDelays(SwitchType::kRtranif1), 2u);
}

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

TEST(PassSwitchDelays, TwoDelaysTurnOnIsFirst) {
  PassSwitchDelaySpec spec{true, true, 10, 20};
  EXPECT_EQ(EffectiveTurnOnDelay(spec), 10u);
}

TEST(PassSwitchDelays, TwoDelaysTurnOffIsSecond) {
  PassSwitchDelaySpec spec{true, true, 10, 20};
  EXPECT_EQ(EffectiveTurnOffDelay(spec), 20u);
}

TEST(PassSwitchDelays, OneDelayAppliesToBoth) {
  PassSwitchDelaySpec spec{true, false, 7, 0};
  EXPECT_EQ(EffectiveTurnOnDelay(spec), 7u);
  EXPECT_EQ(EffectiveTurnOffDelay(spec), 7u);
}

TEST(PassSwitchDelays, NoDelayIsZero) {
  PassSwitchDelaySpec spec{};
  EXPECT_EQ(EffectiveTurnOnDelay(spec), 0u);
  EXPECT_EQ(EffectiveTurnOffDelay(spec), 0u);
}

TEST(PassSwitchDelays, BuiltinXZControlUsesSmallerOfTwo) {
  PassSwitchDelaySpec spec{true, true, 10, 20};
  EXPECT_EQ(EffectiveBuiltinControlXZDelay(spec), 10u);
}

TEST(PassSwitchDelays, BuiltinXZControlSmallerSecondIsUsed) {
  PassSwitchDelaySpec spec{true, true, 20, 10};
  EXPECT_EQ(EffectiveBuiltinControlXZDelay(spec), 10u);
}

TEST(PassSwitchDelays, BuiltinXZControlOneDelayUsesIt) {
  PassSwitchDelaySpec spec{true, false, 5, 0};
  EXPECT_EQ(EffectiveBuiltinControlXZDelay(spec), 5u);
}

TEST(PassSwitchDelays, BuiltinXZControlNoDelayIsZero) {
  PassSwitchDelaySpec spec{};
  EXPECT_EQ(EffectiveBuiltinControlXZDelay(spec), 0u);
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

}
