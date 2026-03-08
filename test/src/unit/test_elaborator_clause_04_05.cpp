// §4.5

#include "fixture_simulator.h"
#include "helpers_scheduler.h"
#include "helpers_scheduler_event.h"
#include "simulator/lowerer.h"
#include "simulator/variable.h"

using namespace delta;

namespace {

TEST(TimeZeroSemantics, TimeZeroSemantics) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "module t;\n"
      "  logic [7:0] a, b;\n"
      "  initial begin\n"
      "    a = 8'd1;\n"
      "    b = a + 8'd1;\n"
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
  EXPECT_EQ(va->value.ToUint64(), 1u);
  EXPECT_EQ(vb->value.ToUint64(), 2u);
}

TEST(CanonicalSimulationSemantics, CanonicalSimulationSemantics) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "module t;\n"
      "  logic [7:0] a, b, c, d;\n"
      "  initial a = 8'd4;\n"
      "  assign b = a + 8'd10;\n"
      "  always_comb c = b - 8'd5;\n"
      "  assign d = c * 8'd2;\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  Lowerer lowerer(f.ctx, f.arena, f.diag);
  lowerer.Lower(design);
  f.scheduler.Run();

  EXPECT_EQ(f.ctx.FindVariable("a")->value.ToUint64(), 4u);
  EXPECT_EQ(f.ctx.FindVariable("b")->value.ToUint64(), 14u);
  EXPECT_EQ(f.ctx.FindVariable("c")->value.ToUint64(), 9u);
  EXPECT_EQ(f.ctx.FindVariable("d")->value.ToUint64(), 18u);
}

}  // namespace
