#include <gtest/gtest.h>

#include "fixture_elaborator.h"
#include "helpers_rtlir_lookup.h"

using namespace delta;

namespace {

TEST(LoopStatementElaboration, WhileLoop) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "module m;\n"
      "  logic [7:0] x;\n"
      "  initial begin\n"
      "    while (x > 0) x = x - 8'd1;\n"
      "  end\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
}

// §12.7.4 repeats a while loop while its condition is true, the truth rule of
// §12.4, and §13.4.3 gives a constant function the meaning it has at run time.
// The condition's only set bit is bit 64, so the body runs, and the fold
// reads 4, only when the evaluator looks above the low 64 bits.
TEST(LoopStatementElaboration, ConstantFunctionWhileReadsBitsAbove63) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "module m;\n"
      "  function automatic int f();\n"
      "    int k = 0;\n"
      "    while (128'h1_0000_0000_0000_0000) begin\n"
      "      k++;\n"
      "      if (k == 4) return k;\n"
      "    end\n"
      "    return 0;\n"
      "  endfunction\n"
      "  localparam int Q = f();\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
  const auto* q = FindParam(design, "m", "Q");
  ASSERT_NE(q, nullptr);
  ASSERT_TRUE(q->is_resolved);
  EXPECT_EQ(q->resolved_value, 4);
}

}  // namespace
