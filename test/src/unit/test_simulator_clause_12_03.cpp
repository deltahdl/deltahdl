// §12.3: Syntax


#include "simulation/lowerer.h"
#include "simulation/variable.h"

#include "fixture_simulator.h"

using namespace delta;

// Sim test fixture
namespace {

// §12.3: statement_item dispatch — all statement kinds execute correctly
// (verifying the dispatcher works across multiple statement types in sequence)
TEST(SimA604, StmtItemDispatchMixed) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "module t;\n"
      "  logic [7:0] a, b, c;\n"
      "  initial begin\n"
      "    a = 8'd1;\n"       // blocking_assignment
      "    if (a == 8'd1)\n"  // conditional_statement
      "      b = 8'd2;\n"
      "    begin\n"  // seq_block
      "      c = a + b;\n"
      "    end\n"
      "  end\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  Lowerer lowerer(f.ctx, f.arena, f.diag);
  lowerer.Lower(design);
  f.scheduler.Run();
  auto* a = f.ctx.FindVariable("a");
  auto* b = f.ctx.FindVariable("b");
  auto* c = f.ctx.FindVariable("c");
  ASSERT_NE(a, nullptr);
  ASSERT_NE(b, nullptr);
  ASSERT_NE(c, nullptr);
  EXPECT_EQ(a->value.ToUint64(), 1u);
  EXPECT_EQ(b->value.ToUint64(), 2u);
  EXPECT_EQ(c->value.ToUint64(), 3u);
}

}  // namespace
