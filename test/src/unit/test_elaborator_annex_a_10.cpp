#include "fixture_elaborator.h"

using namespace delta;

namespace {

TEST(TopLevelGrammarElaboration, RefPortOnModule) {
  EXPECT_TRUE(
      ElabOk("module m(ref int x);\n"
             "endmodule\n"));
}

TEST(TopLevelGrammarElaboration, InoutPortOnModule) {
  EXPECT_TRUE(
      ElabOk("module m(inout wire a);\n"
             "endmodule\n"));
}

TEST(TopLevelGrammarElaboration, TimeunitDeclOk) {
  EXPECT_TRUE(
      ElabOk("module m;\n"
             "  timeunit 1ns;\n"
             "endmodule\n"));
}

TEST(TopLevelGrammarElaboration, TimeprecisionDeclOk) {
  EXPECT_TRUE(
      ElabOk("module m;\n"
             "  timeprecision 1ps;\n"
             "endmodule\n"));
}

TEST(TopLevelGrammarElaboration, TimeunitAndPrecisionOk) {
  EXPECT_TRUE(
      ElabOk("module m;\n"
             "  timeunit 1ns;\n"
             "  timeprecision 1ps;\n"
             "endmodule\n"));
}

TEST(TopLevelGrammarElaboration, ParameterInClassIsLocalparam) {
  EXPECT_TRUE(
      ElabOk("class c;\n"
             "  parameter int WIDTH = 8;\n"
             "endclass\n"
             "module m; endmodule\n"));
}

TEST(TopLevelGrammarElaboration, AutomaticInInitialBlockOk) {
  EXPECT_TRUE(
      ElabOk("module m;\n"
             "  initial begin\n"
             "    automatic int x = 5;\n"
             "  end\n"
             "endmodule\n"));
}

TEST(TopLevelGrammarElaboration, AutomaticInModuleScopeError) {
  ElabFixture f;
  ElaborateSrc(
      "module m;\n"
      "  automatic int x;\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(f.diag.HasErrors());
}

TEST(TopLevelGrammarElaboration, ImportInClassScopeError) {
  ElabFixture f;
  ElaborateSrc(
      "package pkg;\n"
      "  parameter int X = 1;\n"
      "endpackage\n"
      "class c;\n"
      "  import pkg::*;\n"
      "endclass\n"
      "module m; endmodule\n",
      f);
  EXPECT_TRUE(f.diag.HasErrors());
}

TEST(TopLevelGrammarElaboration, VectoredRequiresPackedDim) {
  EXPECT_TRUE(
      ElabOk("module m;\n"
             "  wire vectored [7:0] bus;\n"
             "endmodule\n"));
}

TEST(TopLevelGrammarElaboration, ScalaredRequiresPackedDim) {
  EXPECT_TRUE(
      ElabOk("module m;\n"
             "  wire scalared [3:0] w;\n"
             "endmodule\n"));
}

TEST(TopLevelGrammarElaboration, StructPackedWithDimOk) {
  EXPECT_TRUE(
      ElabOk("module m;\n"
             "  typedef struct packed {\n"
             "    logic [7:0] a;\n"
             "    logic [7:0] b;\n"
             "  } my_t;\n"
             "  my_t data;\n"
             "endmodule\n"));
}

TEST(TopLevelGrammarElaboration, TypeRefWithWireOk) {
  EXPECT_TRUE(
      ElabOk("module m;\n"
             "  wire x;\n"
             "  wire type(x) y;\n"
             "endmodule\n"));
}

TEST(TopLevelGrammarElaboration, TypeRefWithVarOk) {
  EXPECT_TRUE(
      ElabOk("module m;\n"
             "  int x;\n"
             "  var type(x) y;\n"
             "endmodule\n"));
}

TEST(TopLevelGrammarElaboration, DotStarOk) {
  EXPECT_TRUE(
      ElabOk("module sub(input a, output b);\n"
             "  assign b = a;\n"
             "endmodule\n"
             "module m;\n"
             "  logic a, b;\n"
             "  sub u1(.*);\n"
             "endmodule\n"));
}

TEST(TopLevelGrammarElaboration, ReplicationWithConstantOk) {
  EXPECT_TRUE(
      ElabOk("module m;\n"
             "  logic [7:0] x;\n"
             "  assign x = {4{2'b01}};\n"
             "endmodule\n"));
}

TEST(TopLevelGrammarElaboration, EmptyUnpackedArrayConcatOk) {
  EXPECT_TRUE(
      ElabOk("module m;\n"
             "  int q[$];\n"
             "  initial q = {};\n"
             "endmodule\n"));
}

TEST(TopLevelGrammarElaboration, ThisInClassMethodOk) {
  EXPECT_TRUE(
      ElabOk("class c;\n"
             "  int x;\n"
             "  function void set(int v);\n"
             "    this.x = v;\n"
             "  endfunction\n"
             "endclass\n"
             "module m; endmodule\n"));
}

TEST(TopLevelGrammarElaboration, DollarInQueueSelectOk) {
  EXPECT_TRUE(
      ElabOk("module m;\n"
             "  int q[$];\n"
             "  initial q[$] = 5;\n"
             "endmodule\n"));
}

}  // namespace
