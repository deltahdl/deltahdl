#include "elaborator/elaborator.h"
#include "elaborator/rtlir.h"
#include "fixture_elaborator.h"

using namespace delta;

namespace {

TEST(FunctionElaboration, FunctionCallInContAssign) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "module m;\n"
      "  wire [7:0] y;\n"
      "  function logic [7:0] compute(input logic [7:0] a);\n"
      "    return a + 8'd1;\n"
      "  endfunction\n"
      "  assign y = compute(8'd5);\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
}

TEST(FunctionElaboration, ForkJoinIllegalInFunction) {
  ElabFixture f;
  ElaborateSrc(
      "module m;\n"
      "  function void my_func();\n"
      "    fork\n"
      "      a = 1;\n"
      "    join\n"
      "  endfunction\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(f.has_errors);
}

TEST(FunctionElaboration, FunctionWithOutputArgsElaborates) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "module m;\n"
      "  function void compute(input int a, output int b);\n"
      "    b = a * 2;\n"
      "  endfunction\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
}

TEST(FunctionElaboration, FunctionWithRefArgElaborates) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "module m;\n"
      "  function automatic void inc(ref int v);\n"
      "    v = v + 1;\n"
      "  endfunction\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
}

TEST(FunctionElaboration, FunctionEmptyBodyElaborates) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "module m;\n"
      "  function void nop();\n"
      "  endfunction\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
}

TEST(FunctionElaboration, FunctionWithDelayError) {
  ElabFixture f;
  ElaborateSrc(
      "module m;\n"
      "  function void f();\n"
      "    #10;\n"
      "  endfunction\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(f.has_errors);
}

TEST(FunctionElaboration, FunctionEnablesTaskError) {
  ElabFixture f;
  ElaborateSrc(
      "module m;\n"
      "  task t(); endtask\n"
      "  function void f();\n"
      "    t();\n"
      "  endfunction\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(f.has_errors);
}

TEST(FunctionElaboration, EventControlInFunctionIsError) {
  ElabFixture f;
  ElaborateSrc(
      "module m;\n"
      "  logic clk;\n"
      "  function void f();\n"
      "    @(posedge clk);\n"
      "  endfunction\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(f.has_errors);
}

TEST(FunctionElaboration, WaitInFunctionIsError) {
  ElabFixture f;
  ElaborateSrc(
      "module m;\n"
      "  logic ready;\n"
      "  function void f();\n"
      "    wait(ready);\n"
      "  endfunction\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(f.has_errors);
}

TEST(FunctionElaboration, WaitForkInFunctionIsError) {
  ElabFixture f;
  ElaborateSrc(
      "module m;\n"
      "  function void f();\n"
      "    wait fork;\n"
      "  endfunction\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(f.has_errors);
}

TEST(FunctionElaboration, WaitOrderInFunctionIsError) {
  ElabFixture f;
  ElaborateSrc(
      "module m;\n"
      "  event e1, e2;\n"
      "  function void f();\n"
      "    wait_order(e1, e2);\n"
      "  endfunction\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(f.has_errors);
}

TEST(FunctionElaboration, NestedDelayInFunctionIsError) {
  ElabFixture f;
  ElaborateSrc(
      "module m;\n"
      "  function void f();\n"
      "    if (1) begin\n"
      "      #5;\n"
      "    end\n"
      "  endfunction\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(f.has_errors);
}

TEST(FunctionElaboration, FunctionWithNoTimeControlIsOk) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "module m;\n"
      "  function int add(input int a, input int b);\n"
      "    return a + b;\n"
      "  endfunction\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
}

TEST(FunctionElaboration, FunctionCallsFunctionIsOk) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "module m;\n"
      "  function int g(); return 0; endfunction\n"
      "  function int f(); return g(); endfunction\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
}

TEST(FunctionElaboration, ForkJoinAnyIllegalInFunction) {
  ElabFixture f;
  ElaborateSrc(
      "module m;\n"
      "  function void my_func();\n"
      "    fork\n"
      "      a = 1;\n"
      "    join_any\n"
      "  endfunction\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(f.has_errors);
}

TEST(FunctionElaboration, FunctionCallsSystemTaskOk) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "module m;\n"
      "  function void f();\n"
      "    $display(\"hello\");\n"
      "  endfunction\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
}

TEST(FunctionElaboration, FunctionWithNestedTaskEnableError) {
  ElabFixture f;
  ElaborateSrc(
      "module m;\n"
      "  task t(); endtask\n"
      "  function void f();\n"
      "    if (1) begin\n"
      "      t();\n"
      "    end\n"
      "  endfunction\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(f.has_errors);
}

TEST(FunctionElaboration, ForkJoinNoneInFunctionOk) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "module m;\n"
      "  function void f();\n"
      "    fork\n"
      "      $display(\"hi\");\n"
      "    join_none\n"
      "  endfunction\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
}

}  // namespace
