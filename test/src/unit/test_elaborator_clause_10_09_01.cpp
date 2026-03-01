// §10.9.1: Array assignment patterns

#include "fixture_simulator.h"
#include "simulator/lowerer.h"
#include "simulator/scheduler.h"
#include "simulator/sim_context.h"
#include "simulator/variable.h"

using namespace delta;

namespace {

TEST(ElabCh511, ArrayInitPattern_SimpleArrayOk) {
  // §5.11 / §10.9.1: Expressions shall match element for element.
  SimFixture f;
  ElaborateSrc(
      "module top();\n"
      "  int arr[1:0] = '{10, 20};\n"
      "endmodule\n",
      f);
  EXPECT_FALSE(f.diag.HasErrors());
}

// =============================================================================
// A.6.7.1 Patterns — Simulation tests
// =============================================================================
// ---------------------------------------------------------------------------
// assignment_pattern: positional — simulation
// ---------------------------------------------------------------------------
// §10.9: positional assignment pattern packs elements MSB-first
TEST(SimA60701, PositionalPatternPacksMSBFirst) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "module t;\n"
      "  logic [15:0] x;\n"
      "  initial begin\n"
      "    x = '{8'd1, 8'd2};\n"
      "  end\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  Lowerer lowerer(f.ctx, f.arena, f.diag);
  lowerer.Lower(design);
  f.scheduler.Run();
  auto* var = f.ctx.FindVariable("x");
  ASSERT_NE(var, nullptr);
  // '{8'd1, 8'd2} = {8'h01, 8'h02} = 16'h0102 = 258
  EXPECT_EQ(var->value.ToUint64(), 258u);
}

}  // namespace
