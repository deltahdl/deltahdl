// §10.6.2: The force and release procedural statements


#include "simulator/lowerer.h"
#include "simulator/variable.h"

#include "fixture_simulator.h"

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

}  // namespace
