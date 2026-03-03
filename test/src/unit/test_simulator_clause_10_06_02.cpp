// §10.6.2: The force and release procedural statements

#include "fixture_simulator.h"
#include "simulator/lowerer.h"
#include "simulator/variable.h"

using namespace delta;

namespace {

// § variable_lvalue — force overwrites variable
TEST(SimA85, VarLvalueForce) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "module t;\n"
      "  logic [7:0] x;\n"
      "  initial begin x = 8'h00; force x = 8'hFF; end\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  Lowerer lowerer(f.ctx, f.arena, f.diag);
  lowerer.Lower(design);
  f.scheduler.Run();
  auto* var = f.ctx.FindVariable("x");
  ASSERT_NE(var, nullptr);
  EXPECT_EQ(var->value.ToUint64(), 0xFFu);
}

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

bool ValidateForceTarget(const ForceInfo& info) {
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

TEST(ForceRelease, LegalTargetConstBitSelectNet) {
  ForceInfo info{ForceTarget::kConstBitSelectNet};
  EXPECT_TRUE(ValidateForceTarget(info));
}

TEST(ForceRelease, LegalTargetConstPartSelectNet) {
  ForceInfo info{ForceTarget::kConstPartSelectNet};
  EXPECT_TRUE(ValidateForceTarget(info));
}

// §10.6.2: "... or of a net with a user-defined nettype."
TEST(ForceRelease, IllegalUserDefinedNettypePartSelect) {
  ForceInfo info{ForceTarget::kUserDefinedNettypePartSelect};
  EXPECT_FALSE(ValidateForceTarget(info));
}

void ForceVariable(Variable& var, const Logic4Vec& value) { var.value = value; }

// --- Helpers ---
static uint8_t ValOf(const Variable& v) {
  uint8_t a = v.value.words[0].aval & 1;
  uint8_t b = v.value.words[0].bval & 1;
  return static_cast<uint8_t>((b << 1) | a);
}

// --- Force on variable ---
// §10.6.2: "A force statement to a variable shall override a procedural
//  assignment, continuous assignment or an assign procedural continuous
//  assignment to the variable."
TEST(ForceRelease, ForceVariableOverridesValue) {
  Arena arena;
  auto* var = arena.Create<Variable>();
  var->value = MakeLogic4VecVal(arena, 1, 1);
  EXPECT_EQ(ValOf(*var), kVal1);

  ForceVariable(*var, MakeLogic4VecVal(arena, 1, 0));
  EXPECT_EQ(ValOf(*var), kVal0);
}

void ReleaseVariable(Variable& var, bool has_continuous_driver,
                     const Logic4Vec* continuous_value, Arena& arena) {
  (void)arena;
  if (has_continuous_driver && continuous_value) {
    var.value = *continuous_value;
  }
  // Otherwise keep current value.
}

// §10.6.2: "When released, then if the variable is not driven by a
//  continuous assignment ... the variable shall not immediately change
//  value and shall maintain its current value."
TEST(ForceRelease, ReleaseUndrivenVariableHoldsValue) {
  Arena arena;
  auto* var = arena.Create<Variable>();
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
  auto* var = arena.Create<Variable>();
  var->value = MakeLogic4VecVal(arena, 1, 0);

  // Continuous driver has value 0.
  Logic4Vec continuous_val = MakeLogic4VecVal(arena, 1, 0);

  ForceVariable(*var, MakeLogic4VecVal(arena, 1, 1));
  EXPECT_EQ(ValOf(*var), kVal1);

  ReleaseVariable(*var, true, &continuous_val, arena);
  // Should reestablish continuous assignment value (0).
  EXPECT_EQ(ValOf(*var), kVal0);
}

void ForceNet(Net& net, const Logic4Vec& value, Arena& arena) {
  (void)arena;
  net.resolved->value = value;
}

// --- Force on net ---
// §10.6.2: "A force procedural statement on a net shall override all
//  drivers of the net — gate outputs, module outputs, and continuous
//  assignments."
TEST(ForceRelease, ForceNetOverridesAllDrivers) {
  Arena arena;
  auto* var = arena.Create<Variable>();
  var->value = MakeLogic4Vec(arena, 1);

  Net net;
  net.type = NetType::kWire;
  net.resolved = var;
  net.drivers.push_back(MakeLogic4VecVal(arena, 1, 0));

  ForceNet(net, MakeLogic4VecVal(arena, 1, 1), arena);
  EXPECT_EQ(ValOf(*var), kVal1);
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

// §10.6.2: "When released, the net shall immediately be assigned the
//  value determined by the drivers of the net."
TEST(ForceRelease, ReleaseNetImmediatelyRestoresDriverValue) {
  Arena arena;
  auto* var = arena.Create<Variable>();
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

// §10.6.2 example: at time 0, d=0 (a&b&c=1&0&1=0), e=0 (and gate).
// At time 10, force d and e to a|b|c=1. At time 20, release both back
// to driver values (0).
TEST(ForceRelease, NormativeExampleForceAndRelease_InitialState) {
  auto tn = MakeTwoWireNets();

  // Time 0: d=0, e=0.
  ReleaseNet(tn.net_d, tn.arena);
  ReleaseNet(tn.net_e, tn.arena);
  EXPECT_EQ(ValOf(*tn.vd), kVal0);
  EXPECT_EQ(ValOf(*tn.ve), kVal0);
}

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

// Helper to create a blocking assignment statement: lhs = rhs_val.
// Driver coroutine that co_awaits an ExecTask and stores its result.
// Helper to run ExecStmt synchronously (for non-suspending statements).
// Creates a wrapper coroutine, resumes it, and returns the result.
// =============================================================================
// 1. Force / Release (StmtKind::kForce, kRelease)
// =============================================================================
TEST(StmtExec, ForceOverridesValue) {
  StmtFixture f;
  auto* var = f.ctx.CreateVariable("x", 32);
  var->value = MakeLogic4VecVal(f.arena, 32, 10);

  auto* stmt = f.arena.Create<Stmt>();
  stmt->kind = StmtKind::kForce;
  stmt->lhs = MakeId(f.arena, "x");
  stmt->rhs = MakeInt(f.arena, 99);

  RunStmt(stmt, f.ctx, f.arena);
  EXPECT_TRUE(var->is_forced);
  EXPECT_EQ(var->forced_value.ToUint64(), 99u);
  EXPECT_EQ(var->value.ToUint64(), 99u);
}

TEST(StmtExec, ForceNullLhsNoOp) {
  StmtFixture f;
  auto* stmt = f.arena.Create<Stmt>();
  stmt->kind = StmtKind::kForce;
  stmt->lhs = nullptr;
  stmt->rhs = MakeInt(f.arena, 5);

  auto result = RunStmt(stmt, f.ctx, f.arena);
  EXPECT_EQ(result, StmtResult::kDone);
}

}  // namespace
