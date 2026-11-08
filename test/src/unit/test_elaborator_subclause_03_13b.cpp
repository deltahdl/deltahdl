#include <gtest/gtest.h>

#include <cstdint>
#include <string>
#include <string_view>

#include "fixture_elaborator.h"
#include "helpers_reported_error.h"

namespace {

::testing::AssertionResult RedeclaredAt(const std::string& src,
                                        std::string_view message, uint32_t line,
                                        std::string_view subclause) {
  ElabFixture f;
  ElaborateSrc(src, f);
  return ReportedError(f.diag.Diagnostics(), message, line, subclause);
}

TEST(NameSpaceElaboration, NestedNamedBlocksOutsideModuleNameSpaceOk) {
  EXPECT_TRUE(
      ElabOk("module m;\n"
             "  logic inner;\n"
             "  initial begin : a\n"
             "    begin : inner end\n"
             "  end\n"
             "  initial begin : b\n"
             "    begin : inner end\n"
             "  end\n"
             "endmodule\n"));
}

TEST(NameSpaceElaboration, NamedBlockInsideUnnamedBlockOutsideModuleNameSpace) {
  EXPECT_TRUE(
      ElabOk("module m;\n"
             "  logic x;\n"
             "  initial begin\n"
             "    begin : x end\n"
             "  end\n"
             "endmodule\n"));
}

TEST(NameSpaceElaboration, NamedBlockUnderIfClashesWithModuleVariable) {
  EXPECT_TRUE(
      RedeclaredAt("module m;\n"
                   "  logic c;\n"
                   "  initial if (1) begin : c end\n"
                   "endmodule\n",
                   "redeclaration of 'c'", 3, "23.9"));
}

TEST(NameSpaceElaboration, TwoNestedNamedBlocksOfOneNameInOneBlock) {
  EXPECT_TRUE(
      RedeclaredAt("module m;\n"
                   "  initial begin : a\n"
                   "    begin : n end\n"
                   "    begin : n end\n"
                   "  end\n"
                   "endmodule\n",
                   "redeclaration of 'n'", 4, "23.9"));
}

TEST(NameSpaceElaboration, NamedForkSameNameAsVariableError) {
  EXPECT_TRUE(
      RedeclaredAt("module m;\n"
                   "  logic f;\n"
                   "  initial fork : f join\n"
                   "endmodule\n",
                   "redeclaration of 'f'", 3, "23.9"));
}

TEST(NameSpaceElaboration, ParameterSameNameAsVariableError) {
  EXPECT_TRUE(
      RedeclaredAt("module m;\n"
                   "  parameter P = 1;\n"
                   "  logic P;\n"
                   "endmodule\n",
                   "redeclaration of 'P'", 3, "23.9"));
}

TEST(NameSpaceElaboration, TypedefSameNameAsVariableError) {
  EXPECT_TRUE(
      RedeclaredAt("module m;\n"
                   "  typedef int t;\n"
                   "  int t;\n"
                   "endmodule\n",
                   "redeclaration of 't'", 3, "23.9"));
}

TEST(NameSpaceElaboration, GenvarSameNameAsVariableError) {
  EXPECT_TRUE(
      RedeclaredAt("module m;\n"
                   "  genvar g;\n"
                   "  int g;\n"
                   "endmodule\n",
                   "redeclaration of 'g'", 3, "23.9"));
}

TEST(NameSpaceElaboration, ClassSameNameAsVariableError) {
  EXPECT_TRUE(
      RedeclaredAt("module m;\n"
                   "  class C; endclass\n"
                   "  int C;\n"
                   "endmodule\n",
                   "redeclaration of 'C'", 3, "23.9"));
}

TEST(NameSpaceElaboration, LetSameNameAsVariableError) {
  EXPECT_TRUE(
      RedeclaredAt("module m;\n"
                   "  let l = 1;\n"
                   "  logic l;\n"
                   "endmodule\n",
                   "redeclaration of 'l'", 3, "23.9"));
}

TEST(NameSpaceElaboration, CovergroupSameNameAsVariableError) {
  EXPECT_TRUE(
      RedeclaredAt("module m;\n"
                   "  covergroup cg; endgroup\n"
                   "  logic cg;\n"
                   "endmodule\n",
                   "redeclaration of 'cg'", 3, "23.9"));
}

TEST(NameSpaceElaboration, SequenceSameNameAsVariableError) {
  EXPECT_TRUE(
      RedeclaredAt("module m;\n"
                   "  sequence s; 1; endsequence\n"
                   "  logic s;\n"
                   "endmodule\n",
                   "redeclaration of 's'", 3, "23.9"));
}

TEST(NameSpaceElaboration, PropertySameNameAsVariableError) {
  EXPECT_TRUE(
      RedeclaredAt("module m;\n"
                   "  property pr; 1; endproperty\n"
                   "  logic pr;\n"
                   "endmodule\n",
                   "redeclaration of 'pr'", 3, "23.9"));
}

TEST(NameSpaceElaboration, TypedefSameNameAsInstanceError) {
  EXPECT_TRUE(
      RedeclaredAt("module child; endmodule\n"
                   "module m;\n"
                   "  typedef int u;\n"
                   "  child u();\n"
                   "endmodule\n",
                   "redeclaration of 'u'", 4, "23.9"));
}

TEST(NameSpaceElaboration, ModportSameNameAsVariableError) {
  EXPECT_TRUE(
      RedeclaredAt("interface ifc(input logic clk);\n"
                   "  logic a;\n"
                   "  modport mp(input a);\n"
                   "  logic mp;\n"
                   "endinterface\n"
                   "module top;\n"
                   "  logic clk;\n"
                   "  ifc i(clk);\n"
                   "endmodule\n",
                   "redeclaration of 'mp'", 4, "23.9"));
}

TEST(NameSpaceElaboration, ClockingBlockSameNameAsVariableError) {
  EXPECT_TRUE(
      RedeclaredAt("interface ifc(input logic clk);\n"
                   "  clocking cb @(posedge clk); endclocking\n"
                   "  logic cb;\n"
                   "endinterface\n"
                   "module top;\n"
                   "  logic clk;\n"
                   "  ifc i(clk);\n"
                   "endmodule\n",
                   "redeclaration of 'cb'", 3, "23.9"));
}

TEST(NameSpaceElaboration, DefaultClockingReferenceAndForwardTypedefOk) {
  EXPECT_TRUE(
      ElabOk("module m;\n"
             "  logic clk;\n"
             "  clocking cb @(posedge clk); endclocking\n"
             "  default clocking cb;\n"
             "  typedef class C;\n"
             "  class C; endclass\n"
             "endmodule\n"));
}

TEST(NameSpaceElaboration, SecondNetForTypedNonAnsiPortError) {
  EXPECT_TRUE(
      RedeclaredAt("module m(a);\n"
                   "  input a;\n"
                   "  wire a;\n"
                   "  wire a;\n"
                   "endmodule\n",
                   "redeclaration of 'a'", 4, "6.5"));
}

TEST(NameSpaceElaboration, FunctionAndInstanceReuseAnsiPortNames) {
  ElabFixture f;
  ElaborateSrc(
      "module child; endmodule\n"
      "module m(input logic a, output logic b);\n"
      "  function void a(); endfunction\n"
      "  child b();\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(), "redeclaration of port 'a'",
                            3, "3.13"));
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(), "redeclaration of port 'b'",
                            4, "3.13"));
}

TEST(NameSpaceElaboration, TaskAndNamedBlockReuseNonAnsiPortNames) {
  ElabFixture f;
  ElaborateSrc(
      "module m(a, b);\n"
      "  input a;\n"
      "  output b;\n"
      "  task a; endtask\n"
      "  initial begin : b end\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(), "redeclaration of port 'a'",
                            4, "3.13"));
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(), "redeclaration of port 'b'",
                            5, "3.13"));
}

TEST(NameSpaceElaboration, GateAndUdpInstancesReusePortNames) {
  ElabFixture f;
  ElaborateSrc(
      "primitive inv(output o, input i);\n"
      "  table 0 : 1; 1 : 0; endtable\n"
      "endprimitive\n"
      "module m(input logic a, output wire b, output wire c);\n"
      "  and a(b, b, b);\n"
      "  inv c(c, b);\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(), "redeclaration of port 'a'",
                            5, "3.13"));
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(), "redeclaration of port 'c'",
                            6, "3.13"));
}

TEST(NameSpaceElaboration, NamedBlockSameNameAsBlockVariableError) {
  EXPECT_TRUE(
      RedeclaredAt("module m;\n"
                   "  initial begin\n"
                   "    int x;\n"
                   "    begin : x end\n"
                   "  end\n"
                   "endmodule\n",
                   "redeclaration of 'x'", 4, "23.9"));
}

TEST(NameSpaceElaboration, BlockTypedefSameNameAsBlockVariableError) {
  EXPECT_TRUE(
      RedeclaredAt("module m;\n"
                   "  initial begin\n"
                   "    typedef int t;\n"
                   "    int t;\n"
                   "  end\n"
                   "endmodule\n",
                   "redeclaration of 't'", 4, "23.9"));
}

TEST(NameSpaceElaboration, FunctionLocalSameNameAsFormalError) {
  EXPECT_TRUE(
      RedeclaredAt("module m;\n"
                   "  function int f(int a);\n"
                   "    int a;\n"
                   "    return a;\n"
                   "  endfunction\n"
                   "endmodule\n",
                   "redeclaration of 'a'", 3, "23.9"));
}

TEST(NameSpaceElaboration, NamedBlockInFunctionSameNameAsLocalError) {
  EXPECT_TRUE(
      RedeclaredAt("module m;\n"
                   "  task t;\n"
                   "    int x;\n"
                   "    begin : x end\n"
                   "  endtask\n"
                   "endmodule\n",
                   "redeclaration of 'x'", 4, "23.9"));
}

TEST(NameSpaceElaboration, TwoNestedModulesOfOneNameError) {
  EXPECT_TRUE(
      RedeclaredAt("module top;\n"
                   "  module n; endmodule\n"
                   "  module n; endmodule\n"
                   "endmodule\n",
                   "redeclaration of 'n'", 3, "23.9"));
}

TEST(NameSpaceElaboration, NestedCheckerSameNameAsVariableError) {
  EXPECT_TRUE(
      RedeclaredAt("module top;\n"
                   "  checker c; endchecker\n"
                   "  logic c;\n"
                   "endmodule\n",
                   "redeclaration of 'c'", 3, "23.9"));
}

TEST(NameSpaceElaboration, PackageItemsRedeclaredError) {
  ElabFixture f;
  ElaborateSrc(
      "package p;\n"
      "  int a;\n"
      "  int a;\n"
      "  function void f(); endfunction\n"
      "  int f;\n"
      "endpackage\n"
      "module m; endmodule\n",
      f);
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "redeclaration of 'a' in package 'p'", 3, "3.13"));
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "redeclaration of 'f' in package 'p'", 5, "3.13"));
}

TEST(NameSpaceElaboration, PackageForwardTypedefAndClassOk) {
  EXPECT_TRUE(
      ElabOk("package p;\n"
             "  typedef class C;\n"
             "  class C; endclass\n"
             "endpackage\n"
             "module m; endmodule\n"));
}

TEST(NameSpaceElaboration, FunctionReusesCompleteNonAnsiPortName) {
  EXPECT_TRUE(
      RedeclaredAt("module m(a);\n"
                   "  input wire a;\n"
                   "  function void a(); endfunction\n"
                   "endmodule\n",
                   "redeclaration of port 'a'", 3, "3.13"));
}

TEST(NameSpaceElaboration, ExternNestedModuleAndItsDefinitionOk) {
  EXPECT_TRUE(
      ElabOk("module top;\n"
             "  extern module n(input logic a);\n"
             "  module n(input logic a); endmodule\n"
             "endmodule\n"));
}

TEST(NameSpaceElaboration, BlockForwardTypedefAndItsDefinitionOk) {
  EXPECT_TRUE(
      ElabOk("module m;\n"
             "  initial begin\n"
             "    typedef t;\n"
             "    typedef int t;\n"
             "    t v;\n"
             "  end\n"
             "endmodule\n"));
}

}  // namespace
