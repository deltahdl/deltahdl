// §30.3: Specify block declaration


#include "simulation/lowerer.h"
#include "simulation/variable.h"

#include "fixture_simulator.h"

using namespace delta;

namespace {

// Module with specify block containing all item types simulates correctly
TEST(SimA701, SpecifyWithAllItemKindsSimulates) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "module t;\n"
      "  logic [7:0] x;\n"
      "  specify\n"
      "    specparam tPD = 5;\n"
      "    pulsestyle_onevent out1;\n"
      "    showcancelled out2;\n"
      "    (a => b) = tPD;\n"
      "    $setup(data, posedge clk, 10);\n"
      "  endspecify\n"
      "  initial x = 8'd99;\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  Lowerer lowerer(f.ctx, f.arena, f.diag);
  lowerer.Lower(design);
  f.scheduler.Run();
  auto* var = f.ctx.FindVariable("x");
  ASSERT_NE(var, nullptr);
  EXPECT_EQ(var->value.ToUint64(), 99u);
}

// Specify block does not interfere with behavioral initial block execution
TEST(SimA701, SpecifyBlockDoesNotInterfereBehavioral) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "module t;\n"
      "  logic [7:0] a, b;\n"
      "  specify\n"
      "    pulsestyle_ondetect out1;\n"
      "    showcancelled out2;\n"
      "    (x => y) = 10;\n"
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
