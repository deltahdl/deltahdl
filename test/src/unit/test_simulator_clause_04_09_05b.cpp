// §4.9.5: Switch (transistor) processing

#include <gtest/gtest.h>

#include "common/arena.h"
#include "simulation/net.h"
#include "simulation/variable.h"

using namespace delta;

// --- Local types for switch processing ---

enum class SwitchKind : uint8_t {
  kTran,
  kRtran,
  kTranif0,
  kTranif1,
  kRtranif0,
  kRtranif1,
};

struct SwitchInst {
  Net *terminal_a = nullptr;
  Net *terminal_b = nullptr;
  SwitchKind kind = SwitchKind::kTran;
  Logic4Word control{0, 0};
  bool user_defined_nets = false;
};

// --- Implementation ---

static bool SwitchConducts(SwitchKind kind, Logic4Word control) {
  uint8_t c_aval = control.aval & 1;
  uint8_t c_bval = control.bval & 1;
  // 0: aval=0,bval=0  1: aval=1,bval=0  x: aval=0,bval=1  z: aval=1,bval=1
  bool is_one = (c_aval == 1 && c_bval == 0);
  bool is_zero = (c_aval == 0 && c_bval == 0);
  switch (kind) {
  case SwitchKind::kTran:
  case SwitchKind::kRtran:
    return true;
  case SwitchKind::kTranif1:
  case SwitchKind::kRtranif1:
    return is_one;
  case SwitchKind::kTranif0:
  case SwitchKind::kRtranif0:
    return is_zero;
  }
  return false;
}

static bool SwitchControlIsUnknown(SwitchKind kind, Logic4Word control) {
  if (kind == SwitchKind::kTran || kind == SwitchKind::kRtran)
    return false;
  uint8_t c_bval = control.bval & 1;
  return c_bval != 0; // x or z
}

static bool IsZ(const Logic4Word &w) {
  return (w.aval & 1) != 0 && (w.bval & 1) != 0;
}

static Logic4Vec GetDriverValue(const Net &net, const Variable &var) {
  return !net.drivers.empty() ? net.drivers[0] : var.value;
}

static bool IsActiveDriver(const Net &net, const Logic4Vec &drv) {
  return !net.drivers.empty() && !IsZ(drv.words[0]);
}

static void ResolveOneTerminal(Variable &terminal_var,
                               const Logic4Vec &term_drv, bool term_is_driven,
                               const Logic4Vec &other_drv,
                               bool other_is_driven) {
  uint8_t t_a = term_drv.words[0].aval & 1;
  uint8_t t_b = term_drv.words[0].bval & 1;
  uint8_t o_a = other_drv.words[0].aval & 1;
  uint8_t o_b = other_drv.words[0].bval & 1;
  uint8_t on_a = term_is_driven ? t_a : (other_is_driven ? o_a : t_a);
  uint8_t on_b = term_is_driven ? t_b : (other_is_driven ? o_b : t_b);
  uint8_t off_a = term_is_driven ? t_a : 1;
  uint8_t off_b = term_is_driven ? t_b : 1;
  if ((on_a != off_a || on_b != off_b) && !term_is_driven) {
    terminal_var.value.words[0].aval = 0;
    terminal_var.value.words[0].bval = 1;
  }
}

static void ResolveUnknownControlBuiltinSwitch(const SwitchInst &sw) {
  auto &va = *sw.terminal_a->resolved;
  auto &vb = *sw.terminal_b->resolved;
  auto a_driven = GetDriverValue(*sw.terminal_a, va);
  auto b_driven = GetDriverValue(*sw.terminal_b, vb);
  bool a_is_driven = IsActiveDriver(*sw.terminal_a, a_driven);
  bool b_is_driven = IsActiveDriver(*sw.terminal_b, b_driven);
  ResolveOneTerminal(vb, b_driven, b_is_driven, a_driven, a_is_driven);
  ResolveOneTerminal(va, a_driven, a_is_driven, b_driven, b_is_driven);
}

static void PropagateConductingSwitch(const SwitchInst &sw) {
  auto &va = *sw.terminal_a->resolved;
  auto &vb = *sw.terminal_b->resolved;
  auto a_drv = GetDriverValue(*sw.terminal_a, va);
  auto b_drv = GetDriverValue(*sw.terminal_b, vb);
  if (IsZ(a_drv.words[0]) && !IsZ(b_drv.words[0])) {
    va.value.words[0] = b_drv.words[0];
  } else if (IsZ(b_drv.words[0]) && !IsZ(a_drv.words[0])) {
    vb.value.words[0] = a_drv.words[0];
  }
}

static bool HasValidTerminals(const SwitchInst &sw) {
  return sw.terminal_a && sw.terminal_b && sw.terminal_a->resolved &&
         sw.terminal_b->resolved;
}

static void InitializeTerminals(std::vector<SwitchInst> &switches) {
  for (auto &sw : switches) {
    for (auto *net : {sw.terminal_a, sw.terminal_b}) {
      if (net && net->resolved && !net->drivers.empty()) {
        net->resolved->value = net->drivers[0];
      }
    }
  }
}

static void ResolveSwitchFirstPass(std::vector<SwitchInst> &switches) {
  for (auto &sw : switches) {
    if (!HasValidTerminals(sw))
      continue;
    bool conducts = SwitchConducts(sw.kind, sw.control);
    bool unknown_ctrl = SwitchControlIsUnknown(sw.kind, sw.control);
    if (unknown_ctrl && !sw.user_defined_nets) {
      ResolveUnknownControlBuiltinSwitch(sw);
    } else if (conducts && !unknown_ctrl) {
      PropagateConductingSwitch(sw);
    }
  }
}

static void ChainPropagate(std::vector<SwitchInst> &switches) {
  for (auto &sw : switches) {
    if (!HasValidTerminals(sw))
      continue;
    if (!SwitchConducts(sw.kind, sw.control))
      continue;
    if (SwitchControlIsUnknown(sw.kind, sw.control))
      continue;
    auto &va = *sw.terminal_a->resolved;
    auto &vb = *sw.terminal_b->resolved;
    if (IsZ(va.value.words[0]) && !IsZ(vb.value.words[0])) {
      va.value.words[0] = vb.value.words[0];
    } else if (IsZ(vb.value.words[0]) && !IsZ(va.value.words[0])) {
      vb.value.words[0] = va.value.words[0];
    }
  }
}

void ResolveSwitchNetwork(std::vector<SwitchInst> &switches,
                          Arena & /*arena*/) {
  InitializeTerminals(switches);
  ResolveSwitchFirstPass(switches);
  ChainPropagate(switches);
}

// --- Helpers ---

static Net MakeNet1(Arena &arena, Variable *var, uint64_t val) {
  Net net;
  net.type = NetType::kWire;
  net.resolved = var;
  net.drivers.push_back(MakeLogic4VecVal(arena, 1, val));
  return net;
}

static Net MakeUndrivenNet(Arena &arena, Variable *var) {
  Net net;
  net.type = NetType::kWire;
  net.resolved = var;
  auto z = MakeLogic4Vec(arena, 1);
  z.words[0].aval = 1;
  z.words[0].bval = 1;
  net.drivers.push_back(z);
  return net;
}

static uint8_t ValOf(const Variable &v) {
  uint8_t a = v.value.words[0].aval & 1;
  uint8_t b = v.value.words[0].bval & 1;
  return static_cast<uint8_t>((b << 1) | a);
}

static constexpr uint8_t kVal0 = 0;
static constexpr uint8_t kVal1 = 1;
static constexpr uint8_t kValX = 2;
static constexpr uint8_t kValZ = 3;

namespace {

// --- Bidirectional signal flow ---

TEST(SwitchProcessing, TranPropagatesDrivenToUndriven) {
  Arena arena;
  auto *va = arena.Create<Variable>();
  va->value = MakeLogic4Vec(arena, 1);
  auto *vb = arena.Create<Variable>();
  vb->value = MakeLogic4Vec(arena, 1);

  Net a = MakeNet1(arena, va, 1);
  Net b = MakeUndrivenNet(arena, vb);

  std::vector<SwitchInst> sw;
  sw.push_back({&a, &b, SwitchKind::kTran, {}, false});
  ResolveSwitchNetwork(sw, arena);
  EXPECT_EQ(ValOf(*vb), kVal1);
}

TEST(SwitchProcessing, TranBidirectionalPropagation) {
  Arena arena;
  auto *va = arena.Create<Variable>();
  va->value = MakeLogic4Vec(arena, 1);
  auto *vb = arena.Create<Variable>();
  vb->value = MakeLogic4Vec(arena, 1);

  Net a = MakeUndrivenNet(arena, va);
  Net b = MakeNet1(arena, vb, 0);

  std::vector<SwitchInst> sw;
  sw.push_back({&a, &b, SwitchKind::kTran, {}, false});
  ResolveSwitchNetwork(sw, arena);
  EXPECT_EQ(ValOf(*va), kVal0);
}

// --- Coordinated processing ---

TEST(SwitchProcessing, NetworkResolvesAllDevicesTogether) {
  Arena arena;
  auto *va = arena.Create<Variable>();
  va->value = MakeLogic4Vec(arena, 1);
  auto *vb = arena.Create<Variable>();
  vb->value = MakeLogic4Vec(arena, 1);
  auto *vc = arena.Create<Variable>();
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
  auto *va = arena.Create<Variable>();
  va->value = MakeLogic4Vec(arena, 1);
  auto *vb = arena.Create<Variable>();
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
  auto *va = arena.Create<Variable>();
  va->value = MakeLogic4Vec(arena, 1);
  auto *vb = arena.Create<Variable>();
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
  auto *va = arena.Create<Variable>();
  va->value = MakeLogic4Vec(arena, 1);
  auto *vb = arena.Create<Variable>();
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
  auto *va = arena.Create<Variable>();
  va->value = MakeLogic4Vec(arena, 1);
  auto *vb = arena.Create<Variable>();
  vb->value = MakeLogic4Vec(arena, 1);

  Net a = MakeNet1(arena, va, 1);
  Net b = MakeUndrivenNet(arena, vb);

  std::vector<SwitchInst> sw;
  sw.push_back({&a, &b, SwitchKind::kTranif0, {1, 0}, false});
  ResolveSwitchNetwork(sw, arena);
  EXPECT_EQ(ValOf(*vb), kValZ);
}

// --- Built-in net type, x/z control: exhaustive combination ---

TEST(SwitchProcessing, BuiltinNetXControlNonUniqueProducesX) {
  Arena arena;
  auto *va = arena.Create<Variable>();
  va->value = MakeLogic4Vec(arena, 1);
  auto *vb = arena.Create<Variable>();
  vb->value = MakeLogic4Vec(arena, 1);

  Net a = MakeNet1(arena, va, 1);
  Net b = MakeUndrivenNet(arena, vb);

  // control = x: on->b=1, off->b=z. Not unique -> x.
  std::vector<SwitchInst> sw;
  sw.push_back({&a, &b, SwitchKind::kTranif1, {0, 1}, false});
  ResolveSwitchNetwork(sw, arena);
  EXPECT_EQ(ValOf(*vb), kValX);
}

TEST(SwitchProcessing, BuiltinNetZControlNonUniqueProducesX) {
  Arena arena;
  auto *va = arena.Create<Variable>();
  va->value = MakeLogic4Vec(arena, 1);
  auto *vb = arena.Create<Variable>();
  vb->value = MakeLogic4Vec(arena, 1);

  Net a = MakeNet1(arena, va, 0);
  Net b = MakeUndrivenNet(arena, vb);

  // control = z: on->b=0, off->b=z. Not unique -> x.
  std::vector<SwitchInst> sw;
  sw.push_back({&a, &b, SwitchKind::kTranif1, {1, 1}, false});
  ResolveSwitchNetwork(sw, arena);
  EXPECT_EQ(ValOf(*vb), kValX);
}

// --- User-defined net type, x/z control: treated as off ---

TEST(SwitchProcessing, UserDefinedNetXControlTreatedAsOff) {
  Arena arena;
  auto *va = arena.Create<Variable>();
  va->value = MakeLogic4Vec(arena, 1);
  auto *vb = arena.Create<Variable>();
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
  auto *va = arena.Create<Variable>();
  va->value = MakeLogic4Vec(arena, 1);
  auto *vb = arena.Create<Variable>();
  vb->value = MakeLogic4Vec(arena, 1);

  Net a = MakeNet1(arena, va, 1);
  Net b = MakeUndrivenNet(arena, vb);

  std::vector<SwitchInst> sw;
  sw.push_back({&a, &b, SwitchKind::kTranif1, {1, 1}, true});
  ResolveSwitchNetwork(sw, arena);
  EXPECT_EQ(ValOf(*vb), kValZ);
}

// --- User-defined net type: on -> single net, off -> separate ---

TEST(SwitchProcessing, UserDefinedNetControlOnSingleNet) {
  Arena arena;
  auto *va = arena.Create<Variable>();
  va->value = MakeLogic4Vec(arena, 1);
  auto *vb = arena.Create<Variable>();
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
  auto *va = arena.Create<Variable>();
  va->value = MakeLogic4Vec(arena, 1);
  auto *vb = arena.Create<Variable>();
  vb->value = MakeLogic4Vec(arena, 1);

  Net a = MakeNet1(arena, va, 1);
  Net b = MakeUndrivenNet(arena, vb);

  std::vector<SwitchInst> sw;
  sw.push_back({&a, &b, SwitchKind::kTranif1, {0, 0}, true});
  ResolveSwitchNetwork(sw, arena);
  EXPECT_EQ(ValOf(*vb), kValZ);
}

} // namespace
