#include "fixture_elaborator.h"

using namespace delta;

namespace {

// §A.10 clarification 2: ref port shall be variable type;
// inout port shall not be variable type;
// illegal to initialize non-variable-output port

TEST(ElabA10, RefPortOnModule) {
  EXPECT_TRUE(
      ElabOk("module m(ref int x);\n"
             "endmodule\n"));
}

TEST(ElabA10, InoutPortOnModule) {
  EXPECT_TRUE(
      ElabOk("module m(inout wire a);\n"
             "endmodule\n"));
}

// §A.10 clarification 3: timeunits_declaration in non_port item
// must repeat/match previous

TEST(ElabA10, TimeunitDeclOk) {
  EXPECT_TRUE(
      ElabOk("module m;\n"
             "  timeunit 1ns;\n"
             "endmodule\n"));
}

TEST(ElabA10, TimeprecisionDeclOk) {
  EXPECT_TRUE(
      ElabOk("module m;\n"
             "  timeprecision 1ps;\n"
             "endmodule\n"));
}

TEST(ElabA10, TimeunitAndPrecisionOk) {
  EXPECT_TRUE(
      ElabOk("module m;\n"
             "  timeunit 1ns;\n"
             "  timeprecision 1ps;\n"
             "endmodule\n"));
}

// §A.10 clarification 7: parameter in class is synonym for localparam

TEST(ElabA10, ParameterInClassIsLocalparam) {
  EXPECT_TRUE(
      ElabOk("class c;\n"
             "  parameter int WIDTH = 8;\n"
             "endclass\n"
             "module m; endmodule\n"));
}

// §A.10 clarification 14: automatic illegal outside procedural context;
// must have explicit data_type unless var keyword used

TEST(ElabA10, AutomaticInInitialBlockOk) {
  EXPECT_TRUE(
      ElabOk("module m;\n"
             "  initial begin\n"
             "    automatic int x = 5;\n"
             "  end\n"
             "endmodule\n"));
}

TEST(ElabA10, AutomaticInModuleScopeError) {
  ElabFixture f;
  ElaborateSrc(
      "module m;\n"
      "  automatic int x;\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(f.diag.HasErrors());
}

// §A.10 clarification 15: illegal to have import directly within class scope

TEST(ElabA10, ImportInClassScopeError) {
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

// §A.10 clarification 16: charge strength only with trireg;
// vectored/scalared requires packed dimension

TEST(ElabA10, VectoredRequiresPackedDim) {
  EXPECT_TRUE(
      ElabOk("module m;\n"
             "  wire vectored [7:0] bus;\n"
             "endmodule\n"));
}

TEST(ElabA10, ScalaredRequiresPackedDim) {
  EXPECT_TRUE(
      ElabOk("module m;\n"
             "  wire scalared [3:0] w;\n"
             "endmodule\n"));
}

// §A.10 clarification 17: packed keyword required with struct
// when packed dimensions are used

TEST(ElabA10, StructPackedWithDimOk) {
  EXPECT_TRUE(
      ElabOk("module m;\n"
             "  typedef struct packed {\n"
             "    logic [7:0] a;\n"
             "    logic [7:0] b;\n"
             "  } my_t;\n"
             "  my_t data;\n"
             "endmodule\n"));
}

// §A.10 clarification 18: type_reference in net decl preceded by net type
// keyword

TEST(ElabA10, TypeRefWithWireOk) {
  EXPECT_TRUE(
      ElabOk("module m;\n"
             "  wire x;\n"
             "  wire type(x) y;\n"
             "endmodule\n"));
}

TEST(ElabA10, TypeRefWithVarOk) {
  EXPECT_TRUE(
      ElabOk("module m;\n"
             "  int x;\n"
             "  var type(x) y;\n"
             "endmodule\n"));
}

// §A.10 clarification 34: .* at most once in port connections

TEST(ElabA10, DotStarOk) {
  EXPECT_TRUE(
      ElabOk("module sub(input a, output b);\n"
             "  assign b = a;\n"
             "endmodule\n"
             "module m;\n"
             "  logic a, b;\n"
             "  sub u1(.*);\n"
             "endmodule\n"));
}

// §A.10 clarification 39: multiplier in multiple_concatenation
// shall be constant_expression unless string type

TEST(ElabA10, ReplicationWithConstantOk) {
  EXPECT_TRUE(
      ElabOk("module m;\n"
             "  logic [7:0] x;\n"
             "  assign x = {4{2'b01}};\n"
             "endmodule\n"));
}

// §A.10 clarification 40: {} is empty unpacked array concatenation

TEST(ElabA10, EmptyUnpackedArrayConcatOk) {
  EXPECT_TRUE(
      ElabOk("module m;\n"
             "  int q[$];\n"
             "  initial q = {};\n"
             "endmodule\n"));
}

// §A.10 clarification 46: this only in class scope

TEST(ElabA10, ThisInClassMethodOk) {
  EXPECT_TRUE(
      ElabOk("class c;\n"
             "  int x;\n"
             "  function void set(int v);\n"
             "    this.x = v;\n"
             "  endfunction\n"
             "endclass\n"
             "module m; endmodule\n"));
}

// §A.10 clarification 47: $ primary only in queue select

TEST(ElabA10, DollarInQueueSelectOk) {
  EXPECT_TRUE(
      ElabOk("module m;\n"
             "  int q[$];\n"
             "  initial q[$] = 5;\n"
             "endmodule\n"));
}

}  // namespace
