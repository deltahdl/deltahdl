// §30.4.6: Declaring multiple module paths in a single statement


#include "simulation/lowerer.h"
#include "simulation/variable.h"

#include "fixture_simulator.h"

using namespace delta;

namespace {

// Mixed terminal forms do not interfere with behavioral simulation
TEST(SimA703, MixedTerminalFormsDoNotInterfere) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "module t;\n"
      "  logic [7:0] a, b;\n"
      "  specify\n"
      "    (x[3:0], intf.sig *> y[0], z) = 5;\n"
      "    (posedge clk => (q[0] : d)) = 3;\n"
      "  endspecify\n"
      "  initial begin\n"
      "    a = 8'd11;\n"
      "    b = 8'd22;\n"
      "  end\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  Lowerer lowerer(f.ctx, f.arena, f.diag);
  lowerer.Lower(design);
  f.scheduler.Run();
  auto* va = f.ctx.FindVariable("a");
  auto* vb = f.ctx.FindVariable("b");
  ASSERT_NE(va, nullptr);
  ASSERT_NE(vb, nullptr);
  EXPECT_EQ(va->value.ToUint64(), 11u);
  EXPECT_EQ(vb->value.ToUint64(), 22u);
}

}  // namespace
