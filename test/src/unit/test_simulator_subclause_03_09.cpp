#include <gtest/gtest.h>

#include "fixture_simulator.h"
#include "simulator/variable.h"

using namespace delta;

namespace {

TEST(BuildingBlockNameSpace, AProgramsVariableIsItsOwnBesideItsModules) {
  SimFixture f;
  auto* y = RunAndFindVar(
      "program p;\n"
      "  int x = 5;\n"
      "  int y;\n"
      "  initial y = x;\n"
      "endprogram\n"
      "module top;\n"
      "  int x = 9;\n"
      "  p u();\n"
      "endmodule\n",
      f, "u.y");
  EXPECT_FALSE(f.has_errors);
  ASSERT_NE(y, nullptr);
  EXPECT_EQ(y->value.ToUint64(), 5u);
  auto* x = f.ctx.FindVariable("x");
  ASSERT_NE(x, nullptr);
  EXPECT_EQ(x->value.ToUint64(), 9u);
}

TEST(BuildingBlockNameSpace, ACheckersVariableIsItsOwnBesideItsModules) {
  SimFixture f;
  auto* y = RunAndFindVar(
      "checker chk(logic clk);\n"
      "  int x = 5;\n"
      "  int y = x;\n"
      "endchecker\n"
      "module top;\n"
      "  logic clk;\n"
      "  int x = 9;\n"
      "  chk c(clk);\n"
      "endmodule\n",
      f, "c.y");
  EXPECT_FALSE(f.has_errors);
  ASSERT_NE(y, nullptr);
  EXPECT_EQ(y->value.ToUint64(), 5u);
  auto* x = f.ctx.FindVariable("x");
  ASSERT_NE(x, nullptr);
  EXPECT_EQ(x->value.ToUint64(), 9u);
}

TEST(BuildingBlockNameSpace, AChildsTypedefIsItsOwnBesideItsModules) {
  SimFixture f;
  auto* a = RunAndFindVar(
      "module child;\n"
      "  typedef logic [3:0] t;\n"
      "  t a;\n"
      "endmodule\n"
      "module top;\n"
      "  typedef logic [7:0] t;\n"
      "  t b;\n"
      "  child c();\n"
      "endmodule\n",
      f, "c.a");
  EXPECT_FALSE(f.has_errors);
  ASSERT_NE(a, nullptr);
  EXPECT_EQ(a->value.width, 4u);
  auto* b = f.ctx.FindVariable("b");
  ASSERT_NE(b, nullptr);
  EXPECT_EQ(b->value.width, 8u);
}

TEST(BuildingBlockNameSpace, AChildsCallRunsItsOwnFunctionBesideItsModules) {
  SimFixture f;
  auto* y = RunAndFindVar(
      "module child;\n"
      "  function int f();\n"
      "    return 1;\n"
      "  endfunction\n"
      "  int y;\n"
      "  initial y = f();\n"
      "endmodule\n"
      "module top;\n"
      "  function int f();\n"
      "    return 2;\n"
      "  endfunction\n"
      "  child c();\n"
      "endmodule\n",
      f, "c.y");
  EXPECT_FALSE(f.has_errors);
  ASSERT_NE(y, nullptr);
  EXPECT_EQ(y->value.ToUint64(), 1u);
}

TEST(BuildingBlockNameSpace, AModulesVariableIsItsOwnBesideItsModules) {
  SimFixture f;
  auto* y = RunAndFindVar(
      "module child;\n"
      "  int x = 5;\n"
      "  int y;\n"
      "  initial y = x;\n"
      "endmodule\n"
      "module top;\n"
      "  int x = 9;\n"
      "  child c();\n"
      "endmodule\n",
      f, "c.y");
  EXPECT_FALSE(f.has_errors);
  ASSERT_NE(y, nullptr);
  EXPECT_EQ(y->value.ToUint64(), 5u);
  auto* x = f.ctx.FindVariable("x");
  ASSERT_NE(x, nullptr);
  EXPECT_EQ(x->value.ToUint64(), 9u);
}

TEST(BuildingBlockNameSpace, AnInterfacesVariableIsItsOwnBesideItsModules) {
  SimFixture f;
  auto* y = RunAndFindVar(
      "interface ifc;\n"
      "  int x = 5;\n"
      "  int y;\n"
      "  initial y = x;\n"
      "endinterface\n"
      "module top;\n"
      "  int x = 9;\n"
      "  ifc i();\n"
      "endmodule\n",
      f, "i.y");
  EXPECT_FALSE(f.has_errors);
  ASSERT_NE(y, nullptr);
  EXPECT_EQ(y->value.ToUint64(), 5u);
  auto* x = f.ctx.FindVariable("x");
  ASSERT_NE(x, nullptr);
  EXPECT_EQ(x->value.ToUint64(), 9u);
}

TEST(PackageDeclarationSpace, ModuleImportsTypesAndFunctionsOfAPackage) {
  SimFixture f;
  EXPECT_EQ(
      RunCapture("package ComplexPkg;\n"
                 "  typedef struct {\n"
                 "    real i, r;\n"
                 "  } Complex;\n"
                 "  function Complex add(Complex a, b);\n"
                 "    add.r = a.r + b.r;\n"
                 "    add.i = a.i + b.i;\n"
                 "  endfunction\n"
                 "  function Complex mul(Complex a, b);\n"
                 "    mul.r = (a.r * b.r) - (a.i * b.i);\n"
                 "    mul.i = (a.r * b.i) + (a.i * b.r);\n"
                 "  endfunction\n"
                 "endpackage : ComplexPkg\n"
                 "module top;\n"
                 "  import ComplexPkg::*;\n"
                 "  Complex x, y, s, p;\n"
                 "  initial begin\n"
                 "    x.r = 1.0; x.i = 2.0;\n"
                 "    y.r = 3.0; y.i = 4.0;\n"
                 "    s = add(x, y);\n"
                 "    p = mul(x, y);\n"
                 "    $display(\"%0d %0d %0d %0d\", int'(s.r), int'(s.i), "
                 "int'(p.r), int'(p.i));\n"
                 "  end\n"
                 "endmodule\n",
                 f),
      "4 6 -5 10\n");
}

TEST(PackageDeclarationSpace, InterfaceImportsFromAPackage) {
  SimFixture f;
  auto* y = RunAndFindVar(
      "package pk;\n"
      "  localparam int K = 7;\n"
      "endpackage\n"
      "interface ifc;\n"
      "  import pk::K;\n"
      "  int y = K;\n"
      "endinterface\n"
      "module top;\n"
      "  ifc i();\n"
      "endmodule\n",
      f, "i.y");
  EXPECT_FALSE(f.has_errors);
  ASSERT_NE(y, nullptr);
  EXPECT_EQ(y->value.ToUint64(), 7u);
}

TEST(PackageDeclarationSpace, ProgramImportsFromAPackage) {
  SimFixture f;
  auto* y = RunAndFindVar(
      "package pk;\n"
      "  function int triple(int v);\n"
      "    return 3 * v;\n"
      "  endfunction\n"
      "endpackage\n"
      "program p;\n"
      "  import pk::*;\n"
      "  int y;\n"
      "  initial y = triple(4);\n"
      "endprogram\n"
      "module top;\n"
      "  p u();\n"
      "endmodule\n",
      f, "u.y");
  EXPECT_FALSE(f.has_errors);
  ASSERT_NE(y, nullptr);
  EXPECT_EQ(y->value.ToUint64(), 12u);
}

TEST(PackageDeclarationSpace, CheckerImportsFromAPackage) {
  SimFixture f;
  auto* y = RunAndFindVar(
      "package pk;\n"
      "  localparam int K = 11;\n"
      "endpackage\n"
      "checker chk(logic clk);\n"
      "  import pk::*;\n"
      "  int y = K;\n"
      "endchecker\n"
      "module top;\n"
      "  logic clk;\n"
      "  chk c(clk);\n"
      "endmodule\n",
      f, "c.y");
  EXPECT_FALSE(f.has_errors);
  ASSERT_NE(y, nullptr);
  EXPECT_EQ(y->value.ToUint64(), 11u);
}

TEST(PackageDeclarationSpace, PackageImportsFromAnotherPackage) {
  SimFixture f;
  auto* y = RunAndFindVar(
      "package base;\n"
      "  localparam int K = 3;\n"
      "endpackage\n"
      "package derived;\n"
      "  import base::*;\n"
      "  localparam int TWICE = 2 * K;\n"
      "endpackage\n"
      "module top;\n"
      "  import derived::*;\n"
      "  int y = TWICE;\n"
      "endmodule\n",
      f, "y");
  EXPECT_FALSE(f.has_errors);
  ASSERT_NE(y, nullptr);
  EXPECT_EQ(y->value.ToUint64(), 6u);
}

TEST(PackageDeclarationSpace, BlocksImportingAPackageShareItsDeclarations) {
  SimFixture f;
  EXPECT_EQ(RunCapture("package pk;\n"
                       "  int shared_count;\n"
                       "endpackage\n"
                       "module writer;\n"
                       "  import pk::*;\n"
                       "  initial shared_count = 5;\n"
                       "endmodule\n"
                       "module top;\n"
                       "  import pk::shared_count;\n"
                       "  writer w();\n"
                       "  initial #1 $display(\"%0d %0d\", shared_count, "
                       "pk::shared_count);\n"
                       "endmodule\n",
                       f),
            "5 5\n");
}

}  // namespace
