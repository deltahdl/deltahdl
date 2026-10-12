#include <gtest/gtest.h>

#include "fixture_elaborator.h"
#include "fixture_simulator.h"
#include "helpers_rtlir_lookup.h"
#include "simulator/lowerer.h"
#include "simulator/variable.h"

using namespace delta;

namespace {

TEST(ConditionalElaboration, BasicIfElseElaborates) {
  SimFixture f;
  auto* y = RunAndFindVar(
      "module t;\n"
      "  int x, y;\n"
      "  initial begin\n"
      "    x = 10;\n"
      "    if (x == 10)\n"
      "      y = 1;\n"
      "    else\n"
      "      y = 0;\n"
      "  end\n"
      "endmodule\n",
      f, "y");
  ASSERT_NE(y, nullptr);
  EXPECT_EQ(y->value.ToUint64(), 1u);
}

TEST(ConditionalElaboration, MatchesInIfElaborates) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "module t;\n"
      "  logic [7:0] x, y;\n"
      "  initial begin\n"
      "    x = 8'd3;\n"
      "    if (x matches 8'd3) y = 8'd1;\n"
      "    else y = 8'd0;\n"
      "  end\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
}

TEST(ConditionalElaboration, IfElseInAlwaysComb) {
  EXPECT_TRUE(
      ElabOk("module m;\n"
             "  logic a, x;\n"
             "  always_comb begin\n"
             "    if (a) x = 1;\n"
             "    else x = 0;\n"
             "  end\n"
             "endmodule\n"));
}

TEST(ConditionalElaboration, IfWithTripleAndElaborates) {
  EXPECT_TRUE(
      ElabOk("module m;\n"
             "  logic a, b, x;\n"
             "  initial begin\n"
             "    if (a &&& b) x = 1;\n"
             "  end\n"
             "endmodule\n"));
}

TEST(ConditionalElaboration, NestedIfInFunction) {
  EXPECT_TRUE(
      ElabOk("module m;\n"
             "  function int pick(input int a, input int b, input int sel);\n"
             "    if (sel) return a;\n"
             "    else return b;\n"
             "  endfunction\n"
             "endmodule\n"));
}

TEST(ConditionalElaboration, IfWithoutElseElaborates) {
  EXPECT_TRUE(
      ElabOk("module m;\n"
             "  logic a, x;\n"
             "  initial begin\n"
             "    if (a) x = 1;\n"
             "  end\n"
             "endmodule\n"));
}

TEST(ConditionalElaboration, BothBranchesNullElaborates) {
  EXPECT_TRUE(
      ElabOk("module m;\n"
             "  logic a;\n"
             "  initial begin\n"
             "    if (a) ;\n"
             "    else ;\n"
             "  end\n"
             "endmodule\n"));
}

TEST(ConditionalElaboration, NestedIfElseInInitial) {
  EXPECT_TRUE(
      ElabOk("module m;\n"
             "  logic a, b, x;\n"
             "  initial begin\n"
             "    if (a) begin\n"
             "      if (b) x = 1;\n"
             "      else x = 0;\n"
             "    end else begin\n"
             "      x = 0;\n"
             "    end\n"
             "  end\n"
             "endmodule\n"));
}

// §12.4 takes an if's condition as true when its value is known and nonzero,
// and §13.4.3 gives a constant function the meaning it has at run time. The
// condition's only set bit is bit 64, so the fold reads 1 only when the
// evaluator looks above the low 64 bits.
TEST(ConditionalElaboration, ConstantFunctionIfReadsBitsAbove63) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "module m;\n"
      "  function automatic int f();\n"
      "    if (128'h1_0000_0000_0000_0000) return 1;\n"
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
  EXPECT_EQ(q->resolved_value, 1);
}

}  // namespace
