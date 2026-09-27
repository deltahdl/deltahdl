#include <gtest/gtest.h>

#include "fixture_simulator.h"
#include "simulator/lowerer.h"
#include "simulator/net.h"
#include "simulator/variable.h"

using namespace delta;

namespace {

TEST(SequentialBlockSimulation, SeqBlockExecutionOrder) {
  SimFixture f;
  auto* var = RunAndFindVar(
      "module t;\n"
      "  logic [7:0] x;\n"
      "  initial begin\n"
      "    x = 8'd10;\n"
      "    x = 8'd20;\n"
      "  end\n"
      "endmodule\n",
      f, "x");
  ASSERT_NE(var, nullptr);
  EXPECT_EQ(var->value.ToUint64(), 20u);
}

TEST(SequentialBlockSimulation, SeqBlockValuePropagation) {
  SimFixture f;
  auto* var = RunAndFindVar(
      "module t;\n"
      "  logic [7:0] a, b;\n"
      "  initial begin\n"
      "    a = 8'd5;\n"
      "    b = a + 8'd1;\n"
      "  end\n"
      "endmodule\n",
      f, "b");
  ASSERT_NE(var, nullptr);
  EXPECT_EQ(var->value.ToUint64(), 6u);
}

TEST(SequentialBlockSimulation, EmptySeqBlockNoOp) {
  SimFixture f;
  auto* var = RunAndFindVar(
      "module t;\n"
      "  logic [7:0] x;\n"
      "  initial begin\n"
      "    begin\n"
      "    end\n"
      "    x = 8'd42;\n"
      "  end\n"
      "endmodule\n",
      f, "x");
  ASSERT_NE(var, nullptr);
  EXPECT_EQ(var->value.ToUint64(), 42u);
}

TEST(SequentialBlockSimulation, RelativeDelaySemantics) {
  SimFixture f;
  auto* snap = RunAndFindVar(
      "module t;\n"
      "  logic [7:0] x, y;\n"
      "  initial begin\n"
      "    #5 x = 8'd1;\n"
      "    #5 y = 8'd2;\n"
      "  end\n"
      "  logic [7:0] snap_x;\n"
      "  initial begin\n"
      "    #7 snap_x = x;\n"
      "  end\n"
      "endmodule\n",
      f, "snap_x");
  ASSERT_NE(snap, nullptr);
  EXPECT_EQ(snap->value.ToUint64(), 1u);
  auto* y = f.ctx.FindVariable("y");
  ASSERT_NE(y, nullptr);
  EXPECT_EQ(y->value.ToUint64(), 2u);
}

TEST(SequentialBlockSimulation, BlockLocalVarDecl) {
  SimFixture f;
  auto* var = RunAndFindVar(
      "module t;\n"
      "  logic [7:0] result;\n"
      "  initial begin\n"
      "    int tmp;\n"
      "    tmp = 42;\n"
      "    result = tmp[7:0];\n"
      "  end\n"
      "endmodule\n",
      f, "result");
  ASSERT_NE(var, nullptr);
  EXPECT_EQ(var->value.ToUint64(), 42u);
}

TEST(SequentialBlockSimulation, ControlPassesOutAfterDelayedStatements) {
  SimFixture f;
  auto* x_var = RunAndFindVar(
      "module t;\n"
      "  logic [7:0] x, y, after_block;\n"
      "  initial begin\n"
      "    begin\n"
      "      #5 x = 8'd1;\n"
      "      #5 y = 8'd2;\n"
      "    end\n"
      "    after_block = 8'd99;\n"
      "  end\n"
      "endmodule\n",
      f, "x");
  ASSERT_NE(x_var, nullptr);
  EXPECT_EQ(x_var->value.ToUint64(), 1u);
  auto* y_var = f.ctx.FindVariable("y");
  ASSERT_NE(y_var, nullptr);
  EXPECT_EQ(y_var->value.ToUint64(), 2u);
  auto* after = f.ctx.FindVariable("after_block");
  ASSERT_NE(after, nullptr);
  EXPECT_EQ(after->value.ToUint64(), 99u);
}

// §9.3.1 (printed page 225) with §23.9 (printed page 761): a variable an
// unnamed block declares in an instance below the top is that instance's, and
// the block reads back what it writes there, `int`, a packed vector and a
// module typedef alike, in each of two instances. The variable was stored
// where no read from inside the instance reached, and read 0.
TEST(SequentialBlockSimulation, UnnamedBlockLocalOfASubmoduleHoldsItsWrites) {
  SimFixture f;
  EXPECT_EQ(
      RunCapture("module sub;\n"
                 "  typedef logic [5:0] w_t;\n"
                 "  typedef enum { RED, GREEN, BLUE } color_t;\n"
                 "  initial begin\n"
                 "    int i; logic [5:0] l; w_t w; color_t c;\n"
                 "    i = 9; l = 9; w = 9; c = BLUE;\n"
                 "    $display(\"%m i=%0d l=%0d w=%0d wb=%0d c=%s\", i, l, "
                 "w, $bits(w), c.name());\n"
                 "  end\n"
                 "endmodule\n"
                 "module top; sub u(); sub v(); endmodule\n",
                 f),
      "top.u i=9 l=9 w=9 wb=6 c=BLUE\ntop.v i=9 l=9 w=9 wb=6 c=BLUE\n");
}

}  // namespace
