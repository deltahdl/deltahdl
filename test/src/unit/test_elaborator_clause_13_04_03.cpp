#include "fixture_elaborator.h"

using namespace delta;

namespace {

TEST(ElabA82, ConstantFunctionCallInParam) {
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

TEST(Elab1343, ConstantFunctionInputOnlyOk) {
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

TEST(Elab1343, ConstantFunctionOutputArgError) {
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

TEST(Elab1343, ConstantFunctionInoutArgError) {
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

TEST(Elab1343, ConstantFunctionRefArgError) {
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

TEST(Elab1343, ConstantFunctionWithSysFuncOk) {
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

TEST(Elab1343, ConstantFunctionForkError) {
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

TEST(Elab1343, NonConstantContextOutputArgOk) {
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

}
