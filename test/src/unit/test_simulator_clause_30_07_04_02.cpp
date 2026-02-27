// §30.7.4.2: Negative pulse detection


#include "simulation/lowerer.h"
#include "simulation/variable.h"

#include "fixture_simulator.h"

using namespace delta;

namespace {

// Module with showcancelled declarations simulates correctly
TEST(SimA701, SpecifyWithShowcancelledSimulates) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "module t;\n"
      "  logic [7:0] x;\n"
      "  specify\n"
      "    showcancelled out1;\n"
      "    noshowcancelled out2;\n"
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
