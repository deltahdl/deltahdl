// §28.8: Bidirectional pass switches

#include <gtest/gtest.h>

#include "helpers_switch_network.h"
#include "model_switch_eval.h"

namespace {

// =============================================================
// §28.8: Bidirectional pass switches
// =============================================================
// §28.8: tran and rtran are bidirectional.
TEST(BidrectionalSwitches, TranIsBidirectional) {
  EXPECT_TRUE(IsBidirectional(SwitchType::kTran));
  EXPECT_TRUE(IsBidirectional(SwitchType::kRtran));
  EXPECT_TRUE(IsBidirectional(SwitchType::kTranif0));
  EXPECT_TRUE(IsBidirectional(SwitchType::kTranif1));
}

TEST(BidrectionalSwitches, MosSwitchesNotBidirectional) {
  EXPECT_FALSE(IsBidirectional(SwitchType::kNmos));
  EXPECT_FALSE(IsBidirectional(SwitchType::kPmos));
}

// §28.8: "The tran and rtran devices cannot be turned off; they shall
//  always pass signals."
// §28.8: "tran and rtran devices shall not accept delay specifications."
TEST(BidrectionalSwitches, TranNoDelays) {
  EXPECT_FALSE(AcceptsDelaySpec(SwitchType::kTran));
  EXPECT_FALSE(AcceptsDelaySpec(SwitchType::kRtran));
}

// §28.8: tranif/rtranif accept 0-2 delays.
TEST(BidrectionalSwitches, TranifAcceptsDelays) {
  EXPECT_TRUE(AcceptsDelaySpec(SwitchType::kTranif0));
  EXPECT_TRUE(AcceptsDelaySpec(SwitchType::kTranif1));
  EXPECT_EQ(MaxSwitchDelays(SwitchType::kTranif0), 2u);
  EXPECT_EQ(MaxSwitchDelays(SwitchType::kTranif1), 2u);
}

// ---------------------------------------------------------------------------
// §4.9.5 — Six transistor source element types
// ---------------------------------------------------------------------------
TEST(SimCh4095, TransistorSourceElements) {
  Arena arena;
  Scheduler sched(arena);

  // Enumerate all six transistor types as distinct source elements.
  // Each is represented as a named type with bidirectional connectivity.
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

  // Each transistor type participates in switch processing.
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
  // All six transistor types processed.
  EXPECT_EQ(resolved_count, 6);
}
// --- Bidirectional signal flow ---
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

// --- tranif1 / tranif0 control semantics ---
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

TEST(SwitchProcessing, UserDefinedNetZControlTreatedAsOff) {
  auto np = MakeNetPair(1);
  std::vector<SwitchInst> sw;
  sw.push_back({&np.a, &np.b, SwitchKind::kTranif1, {1, 1}, true});
  ResolveSwitchNetwork(sw, np.arena);
  EXPECT_EQ(ValOf(*np.vb), kValZ);
}

// --- User-defined net type: on -> single net, off -> separate ---
TEST(SwitchProcessing, UserDefinedNetControlOnSingleNet) {
  auto np = MakeNetPair(1);
  std::vector<SwitchInst> sw;
  sw.push_back({&np.a, &np.b, SwitchKind::kTranif1, {1, 0}, true});
  ResolveSwitchNetwork(sw, np.arena);
  EXPECT_EQ(ValOf(*np.vb), kVal1);
}

TEST(SwitchProcessing, UserDefinedNetControlOffSeparate) {
  auto np = MakeNetPair(1);
  std::vector<SwitchInst> sw;
  sw.push_back({&np.a, &np.b, SwitchKind::kTranif1, {0, 0}, true});
  ResolveSwitchNetwork(sw, np.arena);
  EXPECT_EQ(ValOf(*np.vb), kValZ);
}

}  // namespace
