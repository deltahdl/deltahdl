// §12.5: Case statement

#include "fixture_simulator.h"
#include "simulator/lowerer.h"
#include "simulator/variable.h"

using namespace delta;

namespace {

// ---------------------------------------------------------------------------
// 9. always_comb case with default branch.
// ---------------------------------------------------------------------------
TEST(SimCh9, AlwaysCombCaseDefault) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "module t;\n"
      "  logic [2:0] sel;\n"
      "  logic [7:0] result;\n"
      "  initial sel = 3'd7;\n"
      "  always_comb begin\n"
      "    case (sel)\n"
      "      3'd0: result = 8'd1;\n"
      "      3'd1: result = 8'd2;\n"
      "      default: result = 8'hFF;\n"
      "    endcase\n"
      "  end\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  Lowerer lowerer(f.ctx, f.arena, f.diag);
  lowerer.Lower(design);
  f.scheduler.Run();
  auto* var = f.ctx.FindVariable("result");
  ASSERT_NE(var, nullptr);
  EXPECT_EQ(var->value.ToUint64(), 0xFFu);
}

}  // namespace
