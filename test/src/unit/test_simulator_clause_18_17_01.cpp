// §18.17.1: Random production weights


#include "simulation/lowerer.h"
#include "simulation/variable.h"

#include "fixture_simulator.h"

using namespace delta;

namespace {

// Weighted alternatives: both are reachable (statistical test)
TEST(SimA612, WeightedAlternativesReachable) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "module t;\n"
      "  logic [7:0] x;\n"
      "  initial begin\n"
      "    x = 8'd0;\n"
      "    randsequence(main)\n"
      "      main : a := 1 | b := 1;\n"
      "      a : { x = 8'd1; };\n"
      "      b : { x = 8'd2; };\n"
      "    endsequence\n"
      "  end\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  Lowerer lowerer(f.ctx, f.arena, f.diag);
  lowerer.Lower(design);
  f.scheduler.Run();
  auto* var = f.ctx.FindVariable("x");
  ASSERT_NE(var, nullptr);
  // One of the alternatives was chosen
  EXPECT_TRUE(var->value.ToUint64() == 1u || var->value.ToUint64() == 2u);
}

}  // namespace
