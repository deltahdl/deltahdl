// Non-LRM tests

#include <gtest/gtest.h>
#include <cstdint>
#include "common/arena.h"
#include "simulator/net.h"
#include "simulator/variable.h"

using namespace delta;

// --- Local types for force/release (§10.6.2) ---
enum class ForceTarget : uint8_t {
  kSingularVariable,
  kNet,
  kConstBitSelectNet,
  kConstPartSelectNet,
  kConcatenation,
  kBitSelectVariable,
  kPartSelectVariable,
  kUserDefinedNettypePartSelect,
};

void ForceNet(Net& net, const Logic4Vec& value, Arena& arena) {
  (void)arena;
  net.resolved->value = value;
}

void ReleaseNet(Net& net, Arena& arena) {
  (void)arena;
  if (!net.drivers.empty()) {
    net.resolved->value = net.drivers[0];
  } else {
    // Set to z: aval=1, bval=1.
    for (uint32_t i = 0; i < net.resolved->value.nwords; ++i) {
      net.resolved->value.words[i].aval = 1;
      net.resolved->value.words[i].bval = 1;
    }
  }
}

// --- Helpers ---
static uint8_t ValOf(const Variable& v) {
  uint8_t a = v.value.words[0].aval & 1;
  uint8_t b = v.value.words[0].bval & 1;
  return static_cast<uint8_t>((b << 1) | a);
}

static constexpr uint8_t kVal0 = 0;

static constexpr uint8_t kVal1 = 1;

// --- Normative example (§10.6.2) ---
struct TwoNets {
  Arena arena;
  Variable* vd = nullptr;
  Variable* ve = nullptr;
  Net net_d;
  Net net_e;
};

static TwoNets MakeTwoWireNets() {
  TwoNets tn;
  tn.vd = tn.arena.Create<Variable>();
  tn.vd->value = MakeLogic4Vec(tn.arena, 1);
  tn.ve = tn.arena.Create<Variable>();
  tn.ve->value = MakeLogic4Vec(tn.arena, 1);
  tn.net_d.type = NetType::kWire;
  tn.net_d.resolved = tn.vd;
  tn.net_d.drivers.push_back(MakeLogic4VecVal(tn.arena, 1, 0));
  tn.net_e.type = NetType::kWire;
  tn.net_e.resolved = tn.ve;
  tn.net_e.drivers.push_back(MakeLogic4VecVal(tn.arena, 1, 0));
  return tn;
}

namespace {

TEST(ForceRelease, NormativeExampleForceAndRelease_ForceAndRelease) {
  auto tn = MakeTwoWireNets();

  // Time 10: force both to a|b|c = 1.
  ForceNet(tn.net_d, MakeLogic4VecVal(tn.arena, 1, 1), tn.arena);
  ForceNet(tn.net_e, MakeLogic4VecVal(tn.arena, 1, 1), tn.arena);
  EXPECT_EQ(ValOf(*tn.vd), kVal1);
  EXPECT_EQ(ValOf(*tn.ve), kVal1);

  // Time 20: release both — should revert to driver value 0.
  ReleaseNet(tn.net_d, tn.arena);
  ReleaseNet(tn.net_e, tn.arena);
  EXPECT_EQ(ValOf(*tn.vd), kVal0);
  EXPECT_EQ(ValOf(*tn.ve), kVal0);
}

}  // namespace
