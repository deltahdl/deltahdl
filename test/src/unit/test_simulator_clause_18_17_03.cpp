// §18.17.3: Case production statements

#include "fixture_simulator.h"
#include "simulator/lowerer.h"
#include "simulator/variable.h"

using namespace delta;

namespace {

// Case in production: selects matching branch
TEST(SimA612, CaseProduction) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "module t;\n"
      "  logic [7:0] x;\n"
      "  initial begin\n"
      "    x = 8'd0;\n"
      "    randsequence(main)\n"
      "      main : case (1) 0: a; 1: b; default: c; endcase;\n"
      "      a : { x = 8'd10; };\n"
      "      b : { x = 8'd20; };\n"
      "      c : { x = 8'd30; };\n"
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
  EXPECT_EQ(var->value.ToUint64(), 20u);
}

}  // namespace
