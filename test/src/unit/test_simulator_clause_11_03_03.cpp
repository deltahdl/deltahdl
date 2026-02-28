// §11.3.3: Using integer literals in expressions

#include "fixture_simulator.h"
#include "simulator/lowerer.h"
#include "simulator/variable.h"

using namespace delta;

namespace {

// =============================================================================
// A.8.4 Primaries — Simulation
// =============================================================================
// § constant_primary — integer literal in parameter
TEST(SimA84, ConstantPrimaryIntegerLiteral) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "module t;\n"
      "  parameter int P = 42;\n"
      "  logic [7:0] x;\n"
      "  initial x = P;\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  Lowerer lowerer(f.ctx, f.arena, f.diag);
  lowerer.Lower(design);
  f.scheduler.Run();
  auto* var = f.ctx.FindVariable("x");
  ASSERT_NE(var, nullptr);
  EXPECT_EQ(var->value.ToUint64(), 42u);
}

}  // namespace
