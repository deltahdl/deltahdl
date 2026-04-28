#include "helpers_scheduler.h"

using namespace delta;

namespace {

TEST(IdentifierSimulation, SimpleIdentVariableResolves) {
  auto val = RunAndGet(
      "module t;\n"
      "  logic [7:0] x;\n"
      "  logic [7:0] y;\n"
      "  initial begin\n"
      "    x = 42;\n"
      "    y = x;\n"
      "  end\n"
      "endmodule\n",
      "y");
  EXPECT_EQ(val, 42u);
}

TEST(IdentifierSimulation, PackageScopeParamResolves) {
  auto val = RunAndGet(
      "package pkg;\n"
      "  parameter int WIDTH = 16;\n"
      "endpackage\n"
      "module t;\n"
      "  logic [31:0] y;\n"
      "  initial y = pkg::WIDTH;\n"
      "endmodule\n",
      "y");
  EXPECT_EQ(val, 16u);
}

TEST(IdentifierSimulation, CaseSensitiveIdentifiers) {
  auto val = RunAndGet(
      "module t;\n"
      "  logic [7:0] x;\n"
      "  logic [7:0] X;\n"
      "  logic [7:0] y;\n"
      "  initial begin\n"
      "    x = 10;\n"
      "    X = 20;\n"
      "    y = x + X;\n"
      "  end\n"
      "endmodule\n",
      "y");
  EXPECT_EQ(val, 30u);
}

TEST(IdentifierSimulation, SystemCallIdentExecutes) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "module t;\n"
      "  initial begin\n"
      "    $display(\"hello\");\n"
      "  end\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  Lowerer lowerer(f.ctx, f.arena, f.diag);
  lowerer.Lower(design);
  f.scheduler.Run();
  EXPECT_FALSE(f.has_errors);
}

TEST(IdentifierSimulation, ParameterIdentResolves) {
  auto val = RunAndGet(
      "module t;\n"
      "  parameter int N = 5;\n"
      "  parameter int M = N * 3;\n"
      "  logic [31:0] y;\n"
      "  initial y = M;\n"
      "endmodule\n",
      "y");
  EXPECT_EQ(val, 15u);
}

TEST(IdentifierSimulation, FunctionIdentCallResolves) {
  auto val = RunAndGet(
      "module t;\n"
      "  function int double_it(int x);\n"
      "    return x * 2;\n"
      "  endfunction\n"
      "  logic [31:0] y;\n"
      "  initial y = double_it(7);\n"
      "endmodule\n",
      "y");
  EXPECT_EQ(val, 14u);
}

TEST(IdentifierSimulation, HierarchicalIdentSubmodulePort) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "module sub(input [7:0] a, output [7:0] b);\n"
      "  assign b = a + 1;\n"
      "endmodule\n"
      "module t;\n"
      "  logic [7:0] x, y;\n"
      "  sub u1(.a(x), .b(y));\n"
      "  initial x = 10;\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  Lowerer lowerer(f.ctx, f.arena, f.diag);
  lowerer.Lower(design);
  f.scheduler.Run();
  auto* var = f.ctx.FindVariable("y");
  ASSERT_NE(var, nullptr);
  EXPECT_EQ(var->value.ToUint64(), 11u);
}

}  // namespace
