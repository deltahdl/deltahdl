// §12.8.2

#include "fixture_simulator.h"
#include "simulator/lowerer.h"
#include "simulator/variable.h"

using namespace delta;

namespace {

// §12.7.4: while with continue
TEST(SimA608, WhileContinue) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "module t;\n"
      "  logic [7:0] x, count;\n"
      "  initial begin\n"
      "    x = 8'd0;\n"
      "    count = 8'd0;\n"
      "    while (x < 8'd6) begin\n"
      "      x = x + 8'd1;\n"
      "      if (x == 8'd3) continue;\n"
      "      count = count + 8'd1;\n"
      "    end\n"
      "  end\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  Lowerer lowerer(f.ctx, f.arena, f.diag);
  lowerer.Lower(design);
  f.scheduler.Run();
  auto* count = f.ctx.FindVariable("count");
  ASSERT_NE(count, nullptr);
  // 6 iterations (x = 1..6), skip x==3 => count = 5
  EXPECT_EQ(count->value.ToUint64(), 5u);
}

}  // namespace
