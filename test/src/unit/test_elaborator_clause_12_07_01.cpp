// §12.7.1: The for-loop

#include "fixture_elaborator.h"
#include "fixture_simulator.h"

using namespace delta;

namespace {

// =============================================================================
// A.6.8 Looping statements — Elaboration
// =============================================================================
// §12.7.1: for loop with typed init elaborates without error
TEST(ElabA608, ForLoopTypedInit) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "module m;\n"
      "  logic [7:0] x;\n"
      "  initial begin\n"
      "    for (int i = 0; i < 10; i++) x = i[7:0];\n"
      "  end\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
}

// §12.7.1: for loop without typed init elaborates without error
TEST(ElabA608, ForLoopUntypedInit) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "module m;\n"
      "  logic [7:0] x;\n"
      "  integer i;\n"
      "  initial begin\n"
      "    for (i = 0; i < 10; i = i + 1) x = i[7:0];\n"
      "  end\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
}

// Nested loops elaborate without error
TEST(ElabA608, NestedLoops) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "module m;\n"
      "  logic [7:0] x;\n"
      "  initial begin\n"
      "    for (int i = 0; i < 4; i++) begin\n"
      "      for (int j = 0; j < 4; j++) begin\n"
      "        x = i[7:0] + j[7:0];\n"
      "      end\n"
      "    end\n"
      "  end\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
}

// ---------------------------------------------------------------------------
// 11. Blocking assignment in for loop (accumulate).
// ---------------------------------------------------------------------------
TEST(SimCh10, BlockingAssignForLoop) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "module t;\n"
      "  int sum;\n"
      "  int i;\n"
      "  initial begin\n"
      "    sum = 0;\n"
      "    for (i = 1; i <= 5; i = i + 1) begin\n"
      "      sum = sum + i;\n"
      "    end\n"
      "  end\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);

  Lowerer lowerer(f.ctx, f.arena, f.diag);
  lowerer.Lower(design);
  f.scheduler.Run();

  auto* var = f.ctx.FindVariable("sum");
  ASSERT_NE(var, nullptr);
  // 1+2+3+4+5 = 15
  EXPECT_EQ(var->value.ToUint64(), 15u);
}

}  // namespace
