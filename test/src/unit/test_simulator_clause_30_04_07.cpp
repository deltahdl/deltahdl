// §30.4.7: Module path polarity


#include "simulation/lowerer.h"
#include "simulation/variable.h"

#include "fixture_simulator.h"

using namespace delta;

namespace {

// Module with polarity path simulates correctly
TEST(SimA702, PolarityPathSimulates) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "module t;\n"
      "  logic [7:0] x;\n"
      "  specify\n"
      "    (a + => b) = 5;\n"
      "    (c - *> d) = 10;\n"
      "  endspecify\n"
      "  initial x = 8'd88;\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  Lowerer lowerer(f.ctx, f.arena, f.diag);
  lowerer.Lower(design);
  f.scheduler.Run();
  auto* var = f.ctx.FindVariable("x");
  ASSERT_NE(var, nullptr);
  EXPECT_EQ(var->value.ToUint64(), 88u);
}

}  // namespace
