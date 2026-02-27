// §12.7.5: The do...while-loop


#include "simulation/lowerer.h"
#include "simulation/variable.h"

#include "fixture_simulator.h"

using namespace delta;

namespace {

// --- do-while ---
// §12.7.5: do-while executes body at least once
TEST(SimA608, DoWhileAtLeastOnce) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "module t;\n"
      "  logic [7:0] x;\n"
      "  initial begin\n"
      "    x = 8'd0;\n"
      "    do x = x + 8'd1; while (0);\n"
      "  end\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  Lowerer lowerer(f.ctx, f.arena, f.diag);
  lowerer.Lower(design);
  f.scheduler.Run();
  auto* var = f.ctx.FindVariable("x");
  ASSERT_NE(var, nullptr);
  // Body executes once even though condition is false
  EXPECT_EQ(var->value.ToUint64(), 1u);
}

// §12.7.5: do-while iterates until condition becomes false
TEST(SimA608, DoWhileIterates) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "module t;\n"
      "  logic [7:0] x;\n"
      "  initial begin\n"
      "    x = 8'd0;\n"
      "    do x = x + 8'd1; while (x < 8'd5);\n"
      "  end\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  Lowerer lowerer(f.ctx, f.arena, f.diag);
  lowerer.Lower(design);
  f.scheduler.Run();
  auto* var = f.ctx.FindVariable("x");
  ASSERT_NE(var, nullptr);
  EXPECT_EQ(var->value.ToUint64(), 5u);
}

}  // namespace
