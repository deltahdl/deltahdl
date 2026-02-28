// §6.8: on variable initialization). This is roughly equivalent to a C
// automatic variable.

#include "fixture_simulator.h"
#include "simulator/lowerer.h"
#include "simulator/net.h"
#include "simulator/variable.h"

using namespace delta;

namespace {

TEST(Lowerer, VariableCreation) {
  LowerFixture f;
  auto* design = ElaborateSrc(
      "module t;\n"
      "  logic [7:0] x;\n"
      "  initial x = 42;\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);

  Lowerer lowerer(f.ctx, f.arena, f.diag);
  lowerer.Lower(design);

  auto* var = f.ctx.FindVariable("x");
  ASSERT_NE(var, nullptr);
}

}  // namespace
