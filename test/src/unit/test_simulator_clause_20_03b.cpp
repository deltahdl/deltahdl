// §20.3: Simulation time system functions


#include "simulator/lowerer.h"
#include "simulator/net.h"
#include "simulator/variable.h"

#include "fixture_simulator.h"

using namespace delta;

namespace {

TEST(Lowerer, RealtimeReturnsTime) {
  LowerFixture f;
  auto* design = ElaborateSrc(
      "module t;\n"
      "  logic [63:0] t_val;\n"
      "  initial begin\n"
      "    #10;\n"
      "    t_val = $realtime;\n"
      "    #1 $finish;\n"
      "  end\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);

  Lowerer lowerer(f.ctx, f.arena, f.diag);
  lowerer.Lower(design);
  f.scheduler.Run();

  auto* var = f.ctx.FindVariable("t_val");
  ASSERT_NE(var, nullptr);
  EXPECT_EQ(var->value.ToUint64(), 10u);
}

}  // namespace
