#include "fixture_elaborator.h"

using namespace delta;

namespace {

TEST(ConstantFunctionElaboration, CallInLocalparam) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "module m;\n"
      "  function int calc(int n); return n * 2; endfunction\n"
      "  localparam int P = calc(4);\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
}

TEST(ConstantFunctionRulesElaboration, InputOnlyArgOk) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "module m;\n"
      "  function int double_val(input int n); return n * 2; endfunction\n"
      "  localparam int P = double_val(4);\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
}

TEST(ConstantFunctionRulesElaboration, OutputArgError) {
  ElabFixture f;
  ElaborateSrc(
      "module m;\n"
      "  function int bad_func(output int n);\n"
      "    n = 0;\n"
      "    return 1;\n"
      "  endfunction\n"
      "  localparam int P = bad_func(4);\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(f.has_errors);
}

TEST(ConstantFunctionRulesElaboration, InoutArgError) {
  ElabFixture f;
  ElaborateSrc(
      "module m;\n"
      "  function int bad_func(inout int n);\n"
      "    return n;\n"
      "  endfunction\n"
      "  localparam int P = bad_func(4);\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(f.has_errors);
}

TEST(ConstantFunctionRulesElaboration, RefArgError) {
  ElabFixture f;
  ElaborateSrc(
      "module m;\n"
      "  function int bad_func(ref int n);\n"
      "    return n;\n"
      "  endfunction\n"
      "  localparam int P = bad_func(4);\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(f.has_errors);
}

TEST(ConstantFunctionRulesElaboration, SystemFunctionCallOk) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "module m;\n"
      "  function int log2_fn(int n); return $clog2(n); endfunction\n"
      "  localparam int W = log2_fn(256);\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
}

TEST(ConstantFunctionRulesElaboration, ForkStatementError) {
  ElabFixture f;
  ElaborateSrc(
      "module m;\n"
      "  function int bad_func(int n);\n"
      "    fork\n"
      "    join_none\n"
      "    return n;\n"
      "  endfunction\n"
      "  localparam int P = bad_func(4);\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(f.has_errors);
}

TEST(ConstantFunctionElaboration, CallInParameterDecl) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "module m;\n"
      "  function int eight(); return 8; endfunction\n"
      "  parameter P = eight();\n"
      "  logic [P-1:0] x;\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
}

TEST(ConstantFunctionElaboration, CallInParameterPortDefault) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "module m #(parameter int P = calc(4));\n"
      "  function int calc(int n); return n * 2; endfunction\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
}

TEST(ConstantFunctionElaboration, NoArgsOk) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "module m;\n"
      "  function int forty_two(); return 42; endfunction\n"
      "  localparam int P = forty_two();\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
}

TEST(ConstantFunctionRulesElaboration, MultipleInputArgsOk) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "module m;\n"
      "  function int add(input int a, input int b);\n"
      "    return a + b;\n"
      "  endfunction\n"
      "  localparam int P = add(10, 32);\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
}

TEST(ConstantFunctionRulesElaboration, ForkNestedInIfError) {
  ElabFixture f;
  ElaborateSrc(
      "module m;\n"
      "  function int bad_func(int n);\n"
      "    if (n > 0) begin\n"
      "      fork\n"
      "      join_none\n"
      "    end\n"
      "    return n;\n"
      "  endfunction\n"
      "  localparam int P = bad_func(4);\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(f.has_errors);
}

TEST(ConstantFunctionRulesElaboration, ForkNestedInLoopError) {
  ElabFixture f;
  ElaborateSrc(
      "module m;\n"
      "  function int bad_func(int n);\n"
      "    for (int i = 0; i < n; i++) begin\n"
      "      fork\n"
      "      join_none\n"
      "    end\n"
      "    return n;\n"
      "  endfunction\n"
      "  localparam int P = bad_func(4);\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(f.has_errors);
}

TEST(ConstantFunctionElaboration, CallInSubExpressionOk) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "module m;\n"
      "  function int calc(int n); return n * 2; endfunction\n"
      "  localparam int P = calc(4) + 1;\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
}

TEST(ConstantFunctionRulesElaboration, NonblockingAssignError) {
  ElabFixture f;
  ElaborateSrc(
      "module m;\n"
      "  function int bad_func(int n);\n"
      "    int tmp;\n"
      "    tmp <= n;\n"
      "    return tmp;\n"
      "  endfunction\n"
      "  localparam int P = bad_func(4);\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(f.has_errors);
}

TEST(ConstantFunctionRulesElaboration, OutputArgInGenerateConditionError) {
  ElabFixture f;
  ElaborateSrc(
      "module m;\n"
      "  function int bad_func(output int n);\n"
      "    n = 0;\n"
      "    return 1;\n"
      "  endfunction\n"
      "  if (bad_func(4)) begin : g\n"
      "    logic x;\n"
      "  end\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(f.has_errors);
}

TEST(ConstantFunctionElaboration, ValidCallInGenerateConditionOk) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "module m;\n"
      "  function int is_wide(int n); return n > 8; endfunction\n"
      "  if (is_wide(16)) begin : g\n"
      "    logic x;\n"
      "  end\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
}

TEST(ConstantFunctionRulesElaboration, NonConstantContextOutputArgOk) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "module m;\n"
      "  function int func_with_output(output int n);\n"
      "    n = 42;\n"
      "    return 1;\n"
      "  endfunction\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
}

}  // namespace
