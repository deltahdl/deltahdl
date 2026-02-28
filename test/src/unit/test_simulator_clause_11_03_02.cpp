// §11.3.2: Operator precedence


#include "simulator/lowerer.h"
#include "simulator/variable.h"

#include "fixture_simulator.h"

using namespace delta;

namespace {

// § expression — precedence: multiply before add
TEST(SimA83, PrecedenceMulBeforeAdd) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "module t;\n"
      "  logic [7:0] x;\n"
      "  initial x = 8'd2 + 8'd3 * 8'd4;\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  Lowerer lowerer(f.ctx, f.arena, f.diag);
  lowerer.Lower(design);
  f.scheduler.Run();
  auto* var = f.ctx.FindVariable("x");
  ASSERT_NE(var, nullptr);
  EXPECT_EQ(var->value.ToUint64(), 14u);
}

}  // namespace
