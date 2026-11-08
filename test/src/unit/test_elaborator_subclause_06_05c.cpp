#include <gtest/gtest.h>

#include <cstdint>
#include <format>
#include <string_view>

#include "fixture_elaborator.h"
#include "helpers_generate_block_items.h"
#include "helpers_reported_error.h"

namespace {

::testing::AssertionResult UsedBeforeDeclared(ElabFixture& f,
                                              std::string_view name,
                                              uint32_t line) {
  return ReportedError(f.diag.Diagnostics(),
                       std::format("'{}' is used before its declaration", name),
                       line, "6.5");
}

TEST(DeclaredBeforeUse, VariableReadAboveItsDeclaration) {
  ElabFixture f;
  ElaborateSrc(
      "module t;\n"
      "  logic a;\n"
      "  initial a = b;\n"
      "  initial if (c) a = 1;\n"
      "  always @(d) a = 0;\n"
      "  logic b, c, d;\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(UsedBeforeDeclared(f, "b", 3));
  EXPECT_TRUE(UsedBeforeDeclared(f, "c", 4));
  EXPECT_TRUE(UsedBeforeDeclared(f, "d", 5));
  EXPECT_TRUE(
      ElabOk("module t;\n"
             "  logic a;\n"
             "  logic b, c, d;\n"
             "  initial a = b;\n"
             "  initial if (c) a = 1;\n"
             "  always @(d) a = 0;\n"
             "endmodule\n"));
}

TEST(DeclaredBeforeUse, VariableWrittenAboveItsDeclaration) {
  ElabFixture f;
  ElaborateSrc(
      "module t;\n"
      "  logic c;\n"
      "  initial b = 1;\n"
      "  always @(c) b[0] <= c;\n"
      "  initial {c, d} = 2'b11;\n"
      "  initial s.p = 1;\n"
      "  logic [1:0] b;\n"
      "  logic d;\n"
      "  struct packed { logic p; } s;\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(UsedBeforeDeclared(f, "b", 3));
  EXPECT_TRUE(UsedBeforeDeclared(f, "b", 4));
  EXPECT_TRUE(UsedBeforeDeclared(f, "d", 5));
  EXPECT_FALSE(UsedBeforeDeclared(f, "c", 5));
  EXPECT_TRUE(UsedBeforeDeclared(f, "s", 6));
  EXPECT_TRUE(
      ElabOk("module t;\n"
             "  logic c;\n"
             "  logic [1:0] b;\n"
             "  logic d;\n"
             "  struct packed { logic p; } s;\n"
             "  initial b = 1;\n"
             "  always @(c) b[0] <= c;\n"
             "  initial {c, d} = 2'b11;\n"
             "  initial s.p = 1;\n"
             "endmodule\n"));
}

TEST(DeclaredBeforeUse, NetUsedAboveItsDeclaration) {
  ElabFixture f;
  ElaborateSrc(
      "module t;\n"
      "  wire a;\n"
      "  assign a = w;\n"
      "  wire w;\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(UsedBeforeDeclared(f, "w", 3));
  ElabFixture driven;
  ElaborateSrc(
      "module t;\n"
      "  assign w = 1'b1;\n"
      "  wire w;\n"
      "endmodule\n",
      driven);
  EXPECT_TRUE(ReportedError(driven.diag.Diagnostics(), "redeclaration of 'w'",
                            3, "6.5"));
  EXPECT_FALSE(UsedBeforeDeclared(driven, "w", 2));
  EXPECT_TRUE(
      ElabOk("module t;\n"
             "  wire a;\n"
             "  wire w;\n"
             "  assign a = w;\n"
             "  assign w = 1'b1;\n"
             "endmodule\n"));
}

TEST(DeclaredBeforeUse, ProceduralContinuousTargetAboveItsDeclaration) {
  ElabFixture f;
  ElaborateSrc(
      "module t;\n"
      "  initial begin\n"
      "    assign a = 1;\n"
      "    deassign a;\n"
      "    force b = 1;\n"
      "    release b;\n"
      "  end\n"
      "  logic a;\n"
      "  wire b;\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(UsedBeforeDeclared(f, "a", 3));
  EXPECT_TRUE(UsedBeforeDeclared(f, "a", 4));
  EXPECT_TRUE(UsedBeforeDeclared(f, "b", 5));
  EXPECT_TRUE(UsedBeforeDeclared(f, "b", 6));
  EXPECT_TRUE(
      ElabOk("module t;\n"
             "  logic a;\n"
             "  wire b;\n"
             "  initial begin\n"
             "    assign a = 1;\n"
             "    deassign a;\n"
             "    force b = 1;\n"
             "    release b;\n"
             "  end\n"
             "endmodule\n"));
}

TEST(DeclaredBeforeUse, ParameterUsedAboveItsDeclaration) {
  ElabFixture f;
  ElaborateSrc(
      "module t;\n"
      "  logic [W-1:0] v;\n"
      "  int u [N];\n"
      "  int k = N;\n"
      "  bit [1:0][N-1:0] m;\n"
      "  localparam W = 4;\n"
      "  parameter N = 2;\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(UsedBeforeDeclared(f, "W", 2));
  EXPECT_TRUE(UsedBeforeDeclared(f, "N", 3));
  EXPECT_TRUE(UsedBeforeDeclared(f, "N", 4));
  EXPECT_TRUE(UsedBeforeDeclared(f, "N", 5));
  EXPECT_TRUE(
      ElabOk("module t;\n"
             "  localparam W = 4;\n"
             "  parameter N = 2;\n"
             "  logic [W-1:0] v;\n"
             "  int u [N];\n"
             "  int k = N;\n"
             "  bit [1:0][N-1:0] m;\n"
             "endmodule\n"));
}

TEST(DeclaredBeforeUse, InterfaceAndProgramUsesAboveTheirDeclarations) {
  ElabFixture f;
  ElaborateSrc(
      "interface i;\n"
      "  initial a = 1;\n"
      "  logic a;\n"
      "endinterface\n"
      "program p;\n"
      "  initial b = 1;\n"
      "  logic b;\n"
      "endprogram\n"
      "module t;\n"
      "  i u();\n"
      "  p q();\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(UsedBeforeDeclared(f, "a", 2));
  EXPECT_TRUE(UsedBeforeDeclared(f, "b", 6));
  EXPECT_TRUE(
      ElabOk("interface i;\n"
             "  logic a;\n"
             "  initial a = 1;\n"
             "endinterface\n"
             "program p;\n"
             "  logic b;\n"
             "  initial b = 1;\n"
             "endprogram\n"
             "module t;\n"
             "  i u();\n"
             "  p q();\n"
             "endmodule\n"));
}

TEST(DeclaredBeforeUse, PackageUsesAboveTheirDeclarations) {
  ElabFixture f;
  ElaborateSrc(
      "package p;\n"
      "  function int f();\n"
      "    return x;\n"
      "  endfunction\n"
      "  logic [W-1:0] v;\n"
      "  int x;\n"
      "  localparam W = 2;\n"
      "endpackage\n"
      "module t;\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(UsedBeforeDeclared(f, "x", 3));
  EXPECT_TRUE(UsedBeforeDeclared(f, "W", 5));
  EXPECT_TRUE(
      ElabOk("package p;\n"
             "  int x;\n"
             "  localparam W = 2;\n"
             "  function int f();\n"
             "    return x;\n"
             "  endfunction\n"
             "  logic [W-1:0] v;\n"
             "endpackage\n"
             "module t;\n"
             "endmodule\n"));
}

TEST(DeclaredBeforeUse, CompilationUnitUsesAboveTheirDeclarations) {
  ElabFixture f;
  ElaborateSrc(
      "function int f();\n"
      "  return x;\n"
      "endfunction\n"
      "logic [W-1:0] v;\n"
      "int x;\n"
      "localparam W = 2;\n"
      "module t;\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(UsedBeforeDeclared(f, "x", 2));
  EXPECT_TRUE(UsedBeforeDeclared(f, "W", 4));
  EXPECT_TRUE(
      ElabOk("int x;\n"
             "localparam W = 2;\n"
             "function int f();\n"
             "  return x;\n"
             "endfunction\n"
             "logic [W-1:0] v;\n"
             "module t;\n"
             "endmodule\n"));
}

TEST(DeclaredBeforeUse, UnitDeclarationAboveTheUseIsTheOneUsed) {
  ElabFixture f;
  ElaborateSrc(
      "module t;\n"
      "  int y;\n"
      "  initial y = x;\n"
      "  int x;\n"
      "endmodule\n"
      "int x;\n",
      f);
  EXPECT_TRUE(UsedBeforeDeclared(f, "x", 3));
  EXPECT_TRUE(
      ElabOk("int x;\n"
             "module t;\n"
             "  int y;\n"
             "  initial y = x;\n"
             "  int x;\n"
             "endmodule\n"));
  EXPECT_TRUE(
      ElabOk("int x;\n"
             "class C;\n"
             "  function void f();\n"
             "    x = 1;\n"
             "  endfunction\n"
             "  int x;\n"
             "endclass\n"
             "module t;\n"
             "endmodule\n"));
}

TEST(DeclaredBeforeUse, ImportedNameIsNoUseAboveTheLocalDeclaration) {
  ElabFixture f;
  ElaborateSrc(
      "package q;\n"
      "  int x;\n"
      "  int y;\n"
      "endpackage\n"
      "package p;\n"
      "  import q::*;\n"
      "  function int f();\n"
      "    return x;\n"
      "  endfunction\n"
      "  int x;\n"
      "endpackage\n"
      "package r;\n"
      "  import q::y;\n"
      "  import elsewhere::*;\n"
      "  function int g();\n"
      "    return y + v;\n"
      "  endfunction\n"
      "  int y;\n"
      "  int v;\n"
      "endpackage\n"
      "module t;\n"
      "  import q::y;\n"
      "  import q::*;\n"
      "  int z;\n"
      "  initial z = y;\n"
      "  initial z = w;\n"
      "  int y;\n"
      "  int w;\n"
      "endmodule\n",
      f);
  EXPECT_FALSE(UsedBeforeDeclared(f, "x", 8));
  EXPECT_FALSE(UsedBeforeDeclared(f, "y", 16));
  EXPECT_FALSE(UsedBeforeDeclared(f, "v", 16));
  EXPECT_FALSE(UsedBeforeDeclared(f, "y", 25));
  EXPECT_TRUE(UsedBeforeDeclared(f, "w", 26));
}

TEST(DeclaredBeforeUse, PortDeclarationAboveTheUseDeclaresIt) {
  EXPECT_TRUE(
      ElabOk("module t(a);\n"
             "  output a;\n"
             "  initial a = 1;\n"
             "  logic a;\n"
             "endmodule\n"));
}

TEST(DeclaredBeforeUse, GenerateBlockUsesAboveTheirDeclarations) {
  ElabFixture f;
  ElaborateSrc(
      "module t;\n"
      "  if (1) begin : g\n"
      "    initial a = 1;\n"
      "    logic a;\n"
      "  end else begin : e\n"
      "    initial c = 1;\n"
      "  end\n"
      "  case (1)\n"
      "    1: begin : k\n"
      "      initial b = 1;\n"
      "    end\n"
      "  endcase\n"
      "  logic b, c;\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(UsedBeforeDeclared(f, "a", 3));
  EXPECT_TRUE(UsedBeforeDeclared(f, "c", 6));
  EXPECT_TRUE(UsedBeforeDeclared(f, "b", 10));
  EXPECT_TRUE(
      ElabOk("module t;\n"
             "  logic b, c;\n"
             "  if (1) begin : g\n"
             "    logic a;\n"
             "    initial a = 1;\n"
             "  end else begin : e\n"
             "    initial c = 1;\n"
             "  end\n"
             "  case (1)\n"
             "    1: begin : k\n"
             "      initial b = 1;\n"
             "    end\n"
             "  endcase\n"
             "  logic a;\n"
             "endmodule\n"));
}

TEST(DeclaredBeforeUse, GenerateConditionAboveItsParameter) {
  ElabFixture f;
  ElaborateSrc(
      "module t;\n"
      "  if (P) begin : g\n"
      "  end\n"
      "  case (1)\n"
      "    Q: begin : k\n"
      "    end\n"
      "  endcase\n"
      "  localparam P = 1;\n"
      "  localparam Q = 1;\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(UsedBeforeDeclared(f, "P", 2));
  EXPECT_TRUE(UsedBeforeDeclared(f, "Q", 5));
  EXPECT_TRUE(
      ElabOk("module t;\n"
             "  localparam P = 1;\n"
             "  localparam Q = 1;\n"
             "  if (P) begin : g\n"
             "  end\n"
             "  case (1)\n"
             "    Q: begin : k\n"
             "    end\n"
             "  endcase\n"
             "endmodule\n"));
}

TEST(DeclaredBeforeUse, NamedBlockUseAboveItsDeclaration) {
  ElabFixture f;
  ElaborateSrc(
      "module t;\n"
      "  initial begin : b\n"
      "    a = 1;\n"
      "  end\n"
      "  logic a;\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(UsedBeforeDeclared(f, "a", 3));
  EXPECT_TRUE(
      ElabOk("module t;\n"
             "  initial begin : b\n"
             "    logic a;\n"
             "    a = 1;\n"
             "  end\n"
             "  logic a;\n"
             "endmodule\n"));
}

TEST(DeclaredBeforeUse, SubroutineUsesAboveTheirDeclarations) {
  ElabFixture f;
  ElaborateSrc(
      "module t;\n"
      "  task tk;\n"
      "    a = 1;\n"
      "  endtask\n"
      "  function int f();\n"
      "    return a;\n"
      "  endfunction\n"
      "  logic a;\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(UsedBeforeDeclared(f, "a", 3));
  EXPECT_TRUE(UsedBeforeDeclared(f, "a", 6));
  EXPECT_TRUE(
      ElabOk("module t;\n"
             "  logic a;\n"
             "  task tk;\n"
             "    a = 1;\n"
             "  endtask\n"
             "  function int f();\n"
             "    return a;\n"
             "  endfunction\n"
             "endmodule\n"));
  EXPECT_TRUE(
      ElabOk("module t;\n"
             "  task tk(output logic a);\n"
             "    a = 1;\n"
             "  endtask\n"
             "  function int f(int a);\n"
             "    return a;\n"
             "  endfunction\n"
             "  logic a;\n"
             "endmodule\n"));
}

TEST(DeclaredBeforeUse, ClassUsesAboveTheirDeclarations) {
  ElabFixture f;
  ElaborateSrc(
      "class C;\n"
      "  function void f();\n"
      "    x = 1;\n"
      "  endfunction\n"
      "  int y = x;\n"
      "  int x;\n"
      "  class I;\n"
      "    task g();\n"
      "      z = 1;\n"
      "    endtask\n"
      "    int z;\n"
      "  endclass\n"
      "endclass\n"
      "module t;\n"
      "  class D;\n"
      "    function int h();\n"
      "      return w;\n"
      "    endfunction\n"
      "    int w;\n"
      "  endclass\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(UsedBeforeDeclared(f, "x", 3));
  EXPECT_TRUE(UsedBeforeDeclared(f, "x", 5));
  EXPECT_TRUE(UsedBeforeDeclared(f, "z", 9));
  EXPECT_TRUE(UsedBeforeDeclared(f, "w", 17));
  EXPECT_TRUE(
      ElabOk("class C;\n"
             "  int x;\n"
             "  int y = x;\n"
             "  function void f();\n"
             "    x = 1;\n"
             "  endfunction\n"
             "  class I;\n"
             "    int z;\n"
             "    task g();\n"
             "      z = 1;\n"
             "    endtask\n"
             "  endclass\n"
             "endclass\n"
             "module t;\n"
             "  class D;\n"
             "    int w;\n"
             "    function int h();\n"
             "      return w;\n"
             "    endfunction\n"
             "  endclass\n"
             "endmodule\n"));
}

TEST(DeclaredBeforeUse, DerivedClassUsesWhatItsBaseMayDeclare) {
  ElabFixture f;
  ElaborateSrc(
      "class B;\n"
      "  int x;\n"
      "endclass\n"
      "class D extends B;\n"
      "  function void f();\n"
      "    x = 1;\n"
      "    y = 1;\n"
      "  endfunction\n"
      "  int x;\n"
      "  int y;\n"
      "endclass\n"
      "module t;\n"
      "endmodule\n",
      f);
  EXPECT_FALSE(UsedBeforeDeclared(f, "x", 6));
  EXPECT_TRUE(UsedBeforeDeclared(f, "y", 7));
  ElabFixture unknown;
  ElaborateSrc(
      "class E extends Missing;\n"
      "  function void f();\n"
      "    z = 1;\n"
      "  endfunction\n"
      "  int z;\n"
      "endclass\n"
      "module t;\n"
      "endmodule\n",
      unknown);
  EXPECT_FALSE(UsedBeforeDeclared(unknown, "z", 3));
}

TEST(DeclaredBeforeUse, SubroutineAssignmentInsideGenerateBlocksJoinsMixture) {
  EXPECT_TRUE(RejectedInsideGenerateBlocks(
      {"", "logic v; assign v = 1;", "task t; v = 0; endtask"},
      "variable 'v' has both continuous and procedural assignments", "6.5"));
  EXPECT_TRUE(AcceptedInsideGenerateBlocks(
      {"", "logic v; initial v = 1;", "task t; v = 0; endtask"}));
}

}  // namespace
