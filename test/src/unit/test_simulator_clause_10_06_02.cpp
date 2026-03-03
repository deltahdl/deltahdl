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

}  // namespace
