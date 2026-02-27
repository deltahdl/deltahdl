// §9.3.3: Statement block start and finish times


#include "simulation/lowerer.h"
#include "simulation/variable.h"

#include "fixture_simulator.h"

using namespace delta;

// Sim test fixture
namespace {

// Nested sequential blocks execute sequentially
TEST(SimA603, NestedSeqBlockExecution) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "module t;\n"
      "  logic [7:0] r;\n"
      "  initial begin\n"
      "    r = 8'd1;\n"
      "    begin\n"
      "      r = r + 8'd1;\n"
      "    end\n"
      "    begin\n"
      "      r = r + 8'd1;\n"
      "    end\n"
      "  end\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  Lowerer lowerer(f.ctx, f.arena, f.diag);
  lowerer.Lower(design);
  f.scheduler.Run();
  auto* var = f.ctx.FindVariable("r");
  ASSERT_NE(var, nullptr);
  EXPECT_EQ(var->value.ToUint64(), 3u);
}

}  // namespace
