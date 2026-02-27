// §30.7.4.1: On-event versus on-detect pulse filtering


#include "simulation/lowerer.h"
#include "simulation/variable.h"

#include "fixture_simulator.h"

using namespace delta;

namespace {

// Module with pulsestyle declarations simulates correctly
TEST(SimA701, SpecifyWithPulsestyleSimulates) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "module t;\n"
      "  logic [7:0] x;\n"
      "  specify\n"
      "    pulsestyle_onevent out1;\n"
      "    pulsestyle_ondetect out2;\n"
      "  endspecify\n"
      "  initial x = 8'd77;\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  Lowerer lowerer(f.ctx, f.arena, f.diag);
  lowerer.Lower(design);
  f.scheduler.Run();
  auto* var = f.ctx.FindVariable("x");
  ASSERT_NE(var, nullptr);
  EXPECT_EQ(var->value.ToUint64(), 77u);
}

}  // namespace
