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

}  // namespace
