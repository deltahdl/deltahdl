#include <gtest/gtest.h>

#include <cstdint>

#include "common/arena.h"
#include "simulation/net.h"
#include "simulation/variable.h"

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

struct ForceInfo {
  ForceTarget target;
  bool has_mixed_assignments = false;
};

bool ValidateForceTarget(const ForceInfo &info);
void ForceVariable(Variable &var, const Logic4Vec &value);
void ReleaseVariable(Variable &var, bool has_continuous_driver,
                     const Logic4Vec *continuous_value, Arena &arena);
void ForceNet(Net &net, const Logic4Vec &value, Arena &arena);
void ReleaseNet(Net &net, Arena &arena);

bool ValidateForceTarget(const ForceInfo &info) {
  if (info.has_mixed_assignments) return false;
  switch (info.target) {
    case ForceTarget::kSingularVariable:
    case ForceTarget::kNet:
    case ForceTarget::kConstBitSelectNet:
    case ForceTarget::kConstPartSelectNet:
    case ForceTarget::kConcatenation:
      return true;
    case ForceTarget::kBitSelectVariable:
    case ForceTarget::kPartSelectVariable:
    case ForceTarget::kUserDefinedNettypePartSelect:
      return false;
  }
  return false;
}

void ForceVariable(Variable &var, const Logic4Vec &value) { var.value = value; }

void ReleaseVariable(Variable &var, bool has_continuous_driver,
                     const Logic4Vec *continuous_value, Arena &arena) {
  (void)arena;
  if (has_continuous_driver && continuous_value) {
    var.value = *continuous_value;
  }
  // Otherwise keep current value.
}

void ForceNet(Net &net, const Logic4Vec &value, Arena &arena) {
  (void)arena;
  net.resolved->value = value;
}

void ReleaseNet(Net &net, Arena &arena) {
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

static uint8_t ValOf(const Variable &v) {
  uint8_t a = v.value.words[0].aval & 1;
  uint8_t b = v.value.words[0].bval & 1;
  return static_cast<uint8_t>((b << 1) | a);
}

static constexpr uint8_t kVal0 = 0;
static constexpr uint8_t kVal1 = 1;

// =============================================================
// §10.6.2: The force and release procedural statements
// =============================================================

// --- Legal LHS targets ---

// §10.6.2: "The left-hand side of the assignment can be a reference to
//  a singular variable, a net, a constant bit-select of a vector net,
//  a constant part-select of a vector net, or a concatenation of these."
TEST(ForceRelease, LegalTargetSingularVariable) {
  ForceInfo info{ForceTarget::kSingularVariable};
  EXPECT_TRUE(ValidateForceTarget(info));
}

TEST(ForceRelease, LegalTargetNet) {
  ForceInfo info{ForceTarget::kNet};
  EXPECT_TRUE(ValidateForceTarget(info));
}

TEST(ForceRelease, LegalTargetConstBitSelectNet) {
  ForceInfo info{ForceTarget::kConstBitSelectNet};
  EXPECT_TRUE(ValidateForceTarget(info));
}

TEST(ForceRelease, LegalTargetConstPartSelectNet) {
  ForceInfo info{ForceTarget::kConstPartSelectNet};
  EXPECT_TRUE(ValidateForceTarget(info));
}

TEST(ForceRelease, LegalTargetConcatenation) {
  ForceInfo info{ForceTarget::kConcatenation};
  EXPECT_TRUE(ValidateForceTarget(info));
}

// --- Illegal LHS targets ---

// §10.6.2: "It shall not be a bit-select or a part-select of a variable."
TEST(ForceRelease, IllegalBitSelectVariable) {
  ForceInfo info{ForceTarget::kBitSelectVariable};
  EXPECT_FALSE(ValidateForceTarget(info));
}

TEST(ForceRelease, IllegalPartSelectVariable) {
  ForceInfo info{ForceTarget::kPartSelectVariable};
  EXPECT_FALSE(ValidateForceTarget(info));
}

// §10.6.2: "... or of a net with a user-defined nettype."
TEST(ForceRelease, IllegalUserDefinedNettypePartSelect) {
  ForceInfo info{ForceTarget::kUserDefinedNettypePartSelect};
  EXPECT_FALSE(ValidateForceTarget(info));
}

// §10.6.2: "A force or release statement shall not be applied to a
//  variable that is being assigned by a mixture of continuous and
//  procedural assignments."
TEST(ForceRelease, IllegalMixedAssignmentTarget) {
  ForceInfo info{ForceTarget::kSingularVariable};
  info.has_mixed_assignments = true;
  EXPECT_FALSE(ValidateForceTarget(info));
}

// --- Force on variable ---

// §10.6.2: "A force statement to a variable shall override a procedural
//  assignment, continuous assignment or an assign procedural continuous
//  assignment to the variable."
TEST(ForceRelease, ForceVariableOverridesValue) {
  Arena arena;
  auto *var = arena.Create<Variable>();
  var->value = MakeLogic4VecVal(arena, 1, 1);
  EXPECT_EQ(ValOf(*var), kVal1);

  ForceVariable(*var, MakeLogic4VecVal(arena, 1, 0));
  EXPECT_EQ(ValOf(*var), kVal0);
}

// §10.6.2: "When released, then if the variable is not driven by a
//  continuous assignment ... the variable shall not immediately change
//  value and shall maintain its current value."
TEST(ForceRelease, ReleaseUndrivenVariableHoldsValue) {
  Arena arena;
  auto *var = arena.Create<Variable>();
  var->value = MakeLogic4VecVal(arena, 1, 0);

  ForceVariable(*var, MakeLogic4VecVal(arena, 1, 1));
  EXPECT_EQ(ValOf(*var), kVal1);

  ReleaseVariable(*var, false, nullptr, arena);
  // Value should remain at forced value (1) since no continuous driver.
  EXPECT_EQ(ValOf(*var), kVal1);
}

// §10.6.2: "Releasing a variable that is driven by a continuous
//  assignment ... shall reestablish that assignment."
TEST(ForceRelease, ReleaseContinuouslyDrivenVariableReestablishes) {
  Arena arena;
  auto *var = arena.Create<Variable>();
  var->value = MakeLogic4VecVal(arena, 1, 0);

  // Continuous driver has value 0.
  Logic4Vec continuous_val = MakeLogic4VecVal(arena, 1, 0);

  ForceVariable(*var, MakeLogic4VecVal(arena, 1, 1));
  EXPECT_EQ(ValOf(*var), kVal1);

  ReleaseVariable(*var, true, &continuous_val, arena);
  // Should reestablish continuous assignment value (0).
  EXPECT_EQ(ValOf(*var), kVal0);
}

// --- Force on net ---

// §10.6.2: "A force procedural statement on a net shall override all
//  drivers of the net — gate outputs, module outputs, and continuous
//  assignments."
TEST(ForceRelease, ForceNetOverridesAllDrivers) {
  Arena arena;
  auto *var = arena.Create<Variable>();
  var->value = MakeLogic4Vec(arena, 1);

  Net net;
  net.type = NetType::kWire;
  net.resolved = var;
  net.drivers.push_back(MakeLogic4VecVal(arena, 1, 0));

  ForceNet(net, MakeLogic4VecVal(arena, 1, 1), arena);
  EXPECT_EQ(ValOf(*var), kVal1);
}

// §10.6.2: "When released, the net shall immediately be assigned the
//  value determined by the drivers of the net."
TEST(ForceRelease, ReleaseNetImmediatelyRestoresDriverValue) {
  Arena arena;
  auto *var = arena.Create<Variable>();
  var->value = MakeLogic4Vec(arena, 1);

  Net net;
  net.type = NetType::kWire;
  net.resolved = var;
  net.drivers.push_back(MakeLogic4VecVal(arena, 1, 0));

  ForceNet(net, MakeLogic4VecVal(arena, 1, 1), arena);
  EXPECT_EQ(ValOf(*var), kVal1);

  ReleaseNet(net, arena);
  // Should immediately restore to driver value (0).
  EXPECT_EQ(ValOf(*var), kVal0);
}

// --- Normative example (§10.6.2) ---

// §10.6.2 example: at time 0, d=0 (a&b&c=1&0&1=0), e=0 (and gate).
// At time 10, force d and e to a|b|c=1. At time 20, release both back
// to driver values (0).
TEST(ForceRelease, NormativeExampleForceAndRelease_InitialState) {
  Arena arena;
  auto *vd = arena.Create<Variable>();
  vd->value = MakeLogic4Vec(arena, 1);
  auto *ve = arena.Create<Variable>();
  ve->value = MakeLogic4Vec(arena, 1);

  Net net_d;
  net_d.type = NetType::kWire;
  net_d.resolved = vd;
  net_d.drivers.push_back(MakeLogic4VecVal(arena, 1, 0));

  Net net_e;
  net_e.type = NetType::kWire;
  net_e.resolved = ve;
  net_e.drivers.push_back(MakeLogic4VecVal(arena, 1, 0));

  // Time 0: d=0, e=0.
  ReleaseNet(net_d, arena);
  ReleaseNet(net_e, arena);
  EXPECT_EQ(ValOf(*vd), kVal0);
  EXPECT_EQ(ValOf(*ve), kVal0);
}

TEST(ForceRelease, NormativeExampleForceAndRelease_ForceAndRelease) {
  Arena arena;
  auto *vd = arena.Create<Variable>();
  vd->value = MakeLogic4Vec(arena, 1);
  auto *ve = arena.Create<Variable>();
  ve->value = MakeLogic4Vec(arena, 1);

  Net net_d;
  net_d.type = NetType::kWire;
  net_d.resolved = vd;
  net_d.drivers.push_back(MakeLogic4VecVal(arena, 1, 0));

  Net net_e;
  net_e.type = NetType::kWire;
  net_e.resolved = ve;
  net_e.drivers.push_back(MakeLogic4VecVal(arena, 1, 0));

  // Time 10: force both to a|b|c = 1.
  ForceNet(net_d, MakeLogic4VecVal(arena, 1, 1), arena);
  ForceNet(net_e, MakeLogic4VecVal(arena, 1, 1), arena);
  EXPECT_EQ(ValOf(*vd), kVal1);
  EXPECT_EQ(ValOf(*ve), kVal1);

  // Time 20: release both — should revert to driver value 0.
  ReleaseNet(net_d, arena);
  ReleaseNet(net_e, arena);
  EXPECT_EQ(ValOf(*vd), kVal0);
  EXPECT_EQ(ValOf(*ve), kVal0);
}
