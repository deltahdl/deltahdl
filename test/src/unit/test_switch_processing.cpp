#include <gtest/gtest.h>

#include "common/arena.h"
#include "simulation/net.h"
#include "simulation/variable.h"

using namespace delta;

// --- Local types for switch processing (§4.9.5) ---

enum class SwitchKind : uint8_t {
  kTran,
  kRtran,
  kTranif0,
  kTranif1,
  kRtranif0,
  kRtranif1,
};

struct SwitchInst {
  Net* terminal_a = nullptr;
  Net* terminal_b = nullptr;
  SwitchKind kind = SwitchKind::kTran;
  Logic4Word control{0, 0};
  bool user_defined_nets = false;
};

void ResolveSwitchNetwork(std::vector<SwitchInst>& switches, Arena& arena);

// --- Helpers ---

static Net MakeNet1(Arena& arena, Variable* var, uint64_t val) {
  Net net;
  net.type = NetType::kWire;
  net.resolved = var;
  net.drivers.push_back(MakeLogic4VecVal(arena, 1, val));
  return net;
}

static Net MakeUndrivenNet(Arena& arena, Variable* var) {
  Net net;
  net.type = NetType::kWire;
  net.resolved = var;
  auto z = MakeLogic4Vec(arena, 1);
  z.words[0].aval = 1;
  z.words[0].bval = 1;
  net.drivers.push_back(z);
  return net;
}

static uint8_t ValOf(const Variable& v) {
  uint8_t a = v.value.words[0].aval & 1;
  uint8_t b = v.value.words[0].bval & 1;
  return static_cast<uint8_t>((b << 1) | a);
}

static constexpr uint8_t kVal0 = 0;
static constexpr uint8_t kVal1 = 1;
static constexpr uint8_t kValX = 2;
static constexpr uint8_t kValZ = 3;

// =============================================================
// §4.9.5: Switch (transistor) processing
// =============================================================

// --- Bidirectional signal flow ---

// §4.9.5: Switches provide bidirectional signal flow.
TEST(SwitchProcessing, TranPropagatesDrivenToUndriven) {
  Arena arena;
  auto* va = arena.Create<Variable>();
  va->value = MakeLogic4Vec(arena, 1);
  auto* vb = arena.Create<Variable>();
  vb->value = MakeLogic4Vec(arena, 1);

  Net a = MakeNet1(arena, va, 1);
  Net b = MakeUndrivenNet(arena, vb);

  std::vector<SwitchInst> sw;
  sw.push_back({&a, &b, SwitchKind::kTran, {}, false});
  ResolveSwitchNetwork(sw, arena);
  EXPECT_EQ(ValOf(*vb), kVal1);
}

// §4.9.5: Bidirectional — driving b propagates to a.
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

// --- Coordinated processing ---

// §4.9.5: "Switch processing shall consider all the devices in a
//  bidirectional switch-connected net before it can determine the
//  appropriate value for any node on the net."
TEST(SwitchProcessing, NetworkResolvesAllDevicesTogether) {
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

  std::vector<SwitchInst> sw;
  sw.push_back({&a, &b, SwitchKind::kTran, {}, false});
  sw.push_back({&b, &c, SwitchKind::kTran, {}, false});
  ResolveSwitchNetwork(sw, arena);
  EXPECT_EQ(ValOf(*vb), kVal1);
  EXPECT_EQ(ValOf(*vc), kVal1);
}

// --- tranif1 / tranif0 control semantics ---

TEST(SwitchProcessing, Tranif1ConductsWhenControlHigh) {
  Arena arena;
  auto* va = arena.Create<Variable>();
  va->value = MakeLogic4Vec(arena, 1);
  auto* vb = arena.Create<Variable>();
  vb->value = MakeLogic4Vec(arena, 1);

  Net a = MakeNet1(arena, va, 1);
  Net b = MakeUndrivenNet(arena, vb);

  std::vector<SwitchInst> sw;
  sw.push_back({&a, &b, SwitchKind::kTranif1, {1, 0}, false});
  ResolveSwitchNetwork(sw, arena);
  EXPECT_EQ(ValOf(*vb), kVal1);
}

TEST(SwitchProcessing, Tranif1BlocksWhenControlLow) {
  Arena arena;
  auto* va = arena.Create<Variable>();
  va->value = MakeLogic4Vec(arena, 1);
  auto* vb = arena.Create<Variable>();
  vb->value = MakeLogic4Vec(arena, 1);

  Net a = MakeNet1(arena, va, 1);
  Net b = MakeUndrivenNet(arena, vb);

  std::vector<SwitchInst> sw;
  sw.push_back({&a, &b, SwitchKind::kTranif1, {0, 0}, false});
  ResolveSwitchNetwork(sw, arena);
  EXPECT_EQ(ValOf(*vb), kValZ);
}

TEST(SwitchProcessing, Tranif0ConductsWhenControlLow) {
  Arena arena;
  auto* va = arena.Create<Variable>();
  va->value = MakeLogic4Vec(arena, 1);
  auto* vb = arena.Create<Variable>();
  vb->value = MakeLogic4Vec(arena, 1);

  Net a = MakeNet1(arena, va, 1);
  Net b = MakeUndrivenNet(arena, vb);

  std::vector<SwitchInst> sw;
  sw.push_back({&a, &b, SwitchKind::kTranif0, {0, 0}, false});
  ResolveSwitchNetwork(sw, arena);
  EXPECT_EQ(ValOf(*vb), kVal1);
}

TEST(SwitchProcessing, Tranif0BlocksWhenControlHigh) {
  Arena arena;
  auto* va = arena.Create<Variable>();
  va->value = MakeLogic4Vec(arena, 1);
  auto* vb = arena.Create<Variable>();
  vb->value = MakeLogic4Vec(arena, 1);

  Net a = MakeNet1(arena, va, 1);
  Net b = MakeUndrivenNet(arena, vb);

  std::vector<SwitchInst> sw;
  sw.push_back({&a, &b, SwitchKind::kTranif0, {1, 0}, false});
  ResolveSwitchNetwork(sw, arena);
  EXPECT_EQ(ValOf(*vb), kValZ);
}

// --- Built-in net type, x/z control: exhaustive combination ---

// §4.9.5: "solve the network repeatedly with these transistors set to
//  all possible combinations ... Any node that has a unique logic level
//  in all cases has steady-state response equal to this level. All
//  other nodes have steady-state response x."
TEST(SwitchProcessing, BuiltinNetXControlNonUniqueProducesX) {
  Arena arena;
  auto* va = arena.Create<Variable>();
  va->value = MakeLogic4Vec(arena, 1);
  auto* vb = arena.Create<Variable>();
  vb->value = MakeLogic4Vec(arena, 1);

  Net a = MakeNet1(arena, va, 1);
  Net b = MakeUndrivenNet(arena, vb);

  // control = x: on→b=1, off→b=z. Not unique → x.
  std::vector<SwitchInst> sw;
  sw.push_back({&a, &b, SwitchKind::kTranif1, {0, 1}, false});
  ResolveSwitchNetwork(sw, arena);
  EXPECT_EQ(ValOf(*vb), kValX);
}

TEST(SwitchProcessing, BuiltinNetZControlNonUniqueProducesX) {
  Arena arena;
  auto* va = arena.Create<Variable>();
  va->value = MakeLogic4Vec(arena, 1);
  auto* vb = arena.Create<Variable>();
  vb->value = MakeLogic4Vec(arena, 1);

  Net a = MakeNet1(arena, va, 0);
  Net b = MakeUndrivenNet(arena, vb);

  // control = z: on→b=0, off→b=z. Not unique → x.
  std::vector<SwitchInst> sw;
  sw.push_back({&a, &b, SwitchKind::kTranif1, {1, 1}, false});
  ResolveSwitchNetwork(sw, arena);
  EXPECT_EQ(ValOf(*vb), kValX);
}

// --- User-defined net type, x/z control: treated as off ---

// §4.9.5: "The bidirectional switch shall be treated as off for an x
//  or z control input value."
TEST(SwitchProcessing, UserDefinedNetXControlTreatedAsOff) {
  Arena arena;
  auto* va = arena.Create<Variable>();
  va->value = MakeLogic4Vec(arena, 1);
  auto* vb = arena.Create<Variable>();
  vb->value = MakeLogic4Vec(arena, 1);

  Net a = MakeNet1(arena, va, 1);
  Net b = MakeUndrivenNet(arena, vb);

  std::vector<SwitchInst> sw;
  sw.push_back({&a, &b, SwitchKind::kTranif1, {0, 1}, true});
  ResolveSwitchNetwork(sw, arena);
  EXPECT_EQ(ValOf(*vb), kValZ);
}

TEST(SwitchProcessing, UserDefinedNetZControlTreatedAsOff) {
  Arena arena;
  auto* va = arena.Create<Variable>();
  va->value = MakeLogic4Vec(arena, 1);
  auto* vb = arena.Create<Variable>();
  vb->value = MakeLogic4Vec(arena, 1);

  Net a = MakeNet1(arena, va, 1);
  Net b = MakeUndrivenNet(arena, vb);

  std::vector<SwitchInst> sw;
  sw.push_back({&a, &b, SwitchKind::kTranif1, {1, 1}, true});
  ResolveSwitchNetwork(sw, arena);
  EXPECT_EQ(ValOf(*vb), kValZ);
}

// --- User-defined net type: on → single net, off → separate ---

// §4.9.5: "If the control input is off, each net is resolved
//  separately; otherwise, they are resolved as if a single net."
TEST(SwitchProcessing, UserDefinedNetControlOnSingleNet) {
  Arena arena;
  auto* va = arena.Create<Variable>();
  va->value = MakeLogic4Vec(arena, 1);
  auto* vb = arena.Create<Variable>();
  vb->value = MakeLogic4Vec(arena, 1);

  Net a = MakeNet1(arena, va, 1);
  Net b = MakeUndrivenNet(arena, vb);

  std::vector<SwitchInst> sw;
  sw.push_back({&a, &b, SwitchKind::kTranif1, {1, 0}, true});
  ResolveSwitchNetwork(sw, arena);
  EXPECT_EQ(ValOf(*vb), kVal1);
}

TEST(SwitchProcessing, UserDefinedNetControlOffSeparate) {
  Arena arena;
  auto* va = arena.Create<Variable>();
  va->value = MakeLogic4Vec(arena, 1);
  auto* vb = arena.Create<Variable>();
  vb->value = MakeLogic4Vec(arena, 1);

  Net a = MakeNet1(arena, va, 1);
  Net b = MakeUndrivenNet(arena, vb);

  std::vector<SwitchInst> sw;
  sw.push_back({&a, &b, SwitchKind::kTranif1, {0, 0}, true});
  ResolveSwitchNetwork(sw, arena);
  EXPECT_EQ(ValOf(*vb), kValZ);
}
