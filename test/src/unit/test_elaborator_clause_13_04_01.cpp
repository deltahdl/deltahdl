#include "elaborator/elaborator.h"
#include "elaborator/rtlir.h"
#include "fixture_elaborator.h"
#include "fixture_simulator.h"

using namespace delta;

namespace {

TEST(FunctionReturnElaboration, FunctionDeclInModule) {
  ElabFixture f;
  auto* design = Elaborate(
      "module m;\n"
      "  function int add(input int a, input int b);\n"
      "    return a + b;\n"
      "  endfunction\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.diag.HasErrors());
}

TEST(FunctionReturnElaboration, VoidFunctionReturnWithValueError) {
  ElabFixture f;
  ElaborateSrc(
      "module m;\n"
      "  function void f();\n"
      "    return 42;\n"
      "  endfunction\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(f.has_errors);
}

TEST(FunctionReturnElaboration, NonVoidFunctionReturnWithValue) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "module m;\n"
      "  function int f();\n"
      "    return 42;\n"
      "  endfunction\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
}

TEST(FunctionReturnElaboration, FunctionCallAsExprElaborates) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "module m;\n"
      "  logic [7:0] x;\n"
      "  function logic [7:0] add_one(input logic [7:0] v);\n"
      "    return v + 8'd1;\n"
      "  endfunction\n"
      "  initial x = add_one(8'd5);\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
}

TEST(FunctionReturnElaboration, NestedCallsElaborate) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "module m;\n"
      "  function int f(int n); return n + 1; endfunction\n"
      "  function int g(int n); return n * 2; endfunction\n"
      "  logic [31:0] x;\n"
      "  initial x = f(g(3));\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
}

TEST(FunctionReturnElaboration, VarSameNameAsFunctionInsideBody) {
  ElabFixture f;
  ElaborateSrc(
      "module m;\n"
      "  function int foo();\n"
      "    int foo;\n"
      "    foo = 1;\n"
      "    return foo;\n"
      "  endfunction\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(f.has_errors);
}

TEST(FunctionReturnElaboration, FunctionNameAssignElaborates) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "module m;\n"
      "  function int compute(input int a);\n"
      "    compute = a * 2;\n"
      "  endfunction\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
}

TEST(FunctionReturnElaboration, FunctionCallReturnsValue) {
  LowerFixture f;
  auto* design = ElaborateSrc(
      "module t;\n"
      "  function int add(input int a, input int b);\n"
      "    return a + b;\n"
      "  endfunction\n"
      "  logic [31:0] x;\n"
      "  initial x = add(10, 32);\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);

  Lowerer lowerer(f.ctx, f.arena, f.diag);
  lowerer.Lower(design);
  f.scheduler.Run();

  auto* var = f.ctx.FindVariable("x");
  ASSERT_NE(var, nullptr);
  EXPECT_EQ(var->value.ToUint64(), 42u);
}

TEST(FunctionReturnElaboration, ReturnStatementElaborates) {
  EXPECT_TRUE(
      ElabOk("module m;\n"
             "  function int add(int a, int b);\n"
             "    return a + b;\n"
             "  endfunction\n"
             "endmodule\n"));
}

TEST(FunctionReturnElaboration, VoidFunctionElaborates) {
  EXPECT_TRUE(
      ElabOk("module m;\n"
             "  function void log(int v);\n"
             "    $display(\"%0d\", v);\n"
             "  endfunction\n"
             "endmodule\n"));
}

TEST(FunctionReturnElaboration, VoidFunctionBareReturnOk) {
  EXPECT_TRUE(
      ElabOk("module m;\n"
             "  function void f();\n"
             "    $display(\"hello\");\n"
             "    return;\n"
             "  endfunction\n"
             "endmodule\n"));
}

TEST(FunctionReturnElaboration, NonVoidFunctionBareReturnOk) {
  EXPECT_TRUE(
      ElabOk("module m;\n"
             "  function int f();\n"
             "    return;\n"
             "  endfunction\n"
             "endmodule\n"));
}

TEST(FunctionReturnElaboration, VoidReturnWithValueInNestedBlockError) {
  ElabFixture f;
  ElaborateSrc(
      "module m;\n"
      "  function void f();\n"
      "    if (1) begin\n"
      "      return 42;\n"
      "    end\n"
      "  endfunction\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(f.has_errors);
}

TEST(FunctionReturnElaboration, VoidFunctionAsOperandError) {
  ElabFixture f;
  ElaborateSrc(
      "module m;\n"
      "  function void nop(); endfunction\n"
      "  logic [31:0] x;\n"
      "  initial x = nop();\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(f.has_errors);
}

TEST(FunctionReturnElaboration, VoidFunctionAsStatementOk) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "module m;\n"
      "  function void nop(); endfunction\n"
      "  initial begin\n"
      "    nop();\n"
      "  end\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
}

TEST(FunctionReturnElaboration, VoidFunctionInContAssignError) {
  ElabFixture f;
  ElaborateSrc(
      "module m;\n"
      "  function void nop(); endfunction\n"
      "  wire w;\n"
      "  assign w = nop();\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(f.has_errors);
}

TEST(FunctionReturnElaboration, VoidFunctionAsArgError) {
  ElabFixture f;
  ElaborateSrc(
      "module m;\n"
      "  function void nop(); endfunction\n"
      "  function int f(int x); return x; endfunction\n"
      "  logic [31:0] x;\n"
      "  initial x = f(nop());\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(f.has_errors);
}

}  // namespace
