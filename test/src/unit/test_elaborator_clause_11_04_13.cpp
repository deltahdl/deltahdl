#include "fixture_simulator.h"
#include "helpers_clocking.h"
#include "helpers_eval_op.h"
#include "helpers_lower_run.h"
#include "helpers_scheduler.h"

using namespace delta;

namespace {

// §11.4.13: if no match is found the operator returns 1'b0. Driven through the
// full pipeline so both the left-hand side and the value set come from real
// literals: 4 is not a member of {3,5,7}.
TEST(ExpressionSim, InsideValueNoMatch) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "module t;\n"
      "  logic x;\n"
      "  initial x = 8'd4 inside {8'd3, 8'd5, 8'd7};\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  Lowerer lowerer(f.ctx, f.arena, f.diag);
  lowerer.Lower(design);
  f.scheduler.Run();
  auto* var = f.ctx.FindVariable("x");
  ASSERT_NE(var, nullptr);
  EXPECT_EQ(var->value.ToUint64(), 0u);
}

// §11.4.13: integral comparisons use wildcard equality, so an x or z bit in a
// set value is a do-not-care in that position. `3'b1?1` matches 3'b101 because
// the wildcard bit ignores val's middle bit.
TEST(ExpressionSim, InsideWildcardRhsMatch) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "module t;\n"
      "  logic [2:0] val;\n"
      "  logic x;\n"
      "  initial begin\n"
      "    val = 3'b101;\n"
      "    x = val inside {3'b1?1};\n"
      "  end\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  Lowerer lowerer(f.ctx, f.arena, f.diag);
  lowerer.Lower(design);
  f.scheduler.Run();
  auto* var = f.ctx.FindVariable("x");
  ASSERT_NE(var, nullptr);
  EXPECT_EQ(var->value.ToUint64(), 1u);
}

// §11.4.13: a match is found when the left-hand side lies inclusively within
// the range, so both the low and the high bound are themselves matches.
TEST(ExpressionSim, InsideRangeBoundaryInclusive) {
  SimFixture f;
  auto [x, y] = RunModuleTwoVars(f,
                                 "module t;\n"
                                 "  logic x, y;\n"
                                 "  initial begin\n"
                                 "    x = 8'd5 inside {[8'd5:8'd10]};\n"
                                 "    y = 8'd10 inside {[8'd5:8'd10]};\n"
                                 "  end\n"
                                 "endmodule\n",
                                 "x", "y");
  EXPECT_EQ(x, 1u);
  EXPECT_EQ(y, 1u);
}

}  // namespace
