#include "fixture_parser.h"

using namespace delta;

namespace {

// §A.10 clarification 1: package_import_declaration in ansi header
// shall be followed by parameter_port_list or list_of_port_declarations

TEST(ParserA10, ImportInHeaderFollowedByPorts) {
  auto r = Parse(
      "module m import pkg::*; (input a, output b);\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  EXPECT_EQ(r.cu->modules[0]->ports.size(), 2u);
}

TEST(ParserA10, ImportInHeaderFollowedByParams) {
  auto r = Parse(
      "module m import pkg::*; #(parameter int W = 8) (input a);\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
}

TEST(ParserA10, ImportInHeaderFollowedByBoth) {
  auto r = Parse(
      "module m import pkg::*; #(parameter int W = 8) (input a, output b);\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
}

// §A.10 clarification 14: automatic keyword illegal outside procedural context

TEST(ParserA10, AutomaticInProceduralBlockOk) {
  EXPECT_TRUE(
      ParseOk("module m;\n"
              "  initial begin\n"
              "    automatic int x = 5;\n"
              "  end\n"
              "endmodule\n"));
}

// §A.10 clarification 22: omitting constant_param_expression
// legal in parameter_port_list but not in localparam

TEST(ParserA10, ParamOmitValueInPortList) {
  auto r = Parse(
      "module m #(parameter int W) (input [W-1:0] d);\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
}

TEST(ParserA10, TypeParamOmitTypeInPortList) {
  auto r = Parse(
      "module m #(parameter type T) ();\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
}

// §A.10 clarification 30: matches operator has higher precedence than && and ||

TEST(ParserA10, MatchesPrecedenceOverLogicalAnd) {
  EXPECT_TRUE(
      ParseOk("module m;\n"
              "  initial begin\n"
              "    if (x matches 1 && y matches 2)\n"
              "      $display(\"ok\");\n"
              "  end\n"
              "endmodule\n"));
}

// §A.10 clarification 34: .* shall appear at most once

TEST(ParserA10, DotStarOnceInPortConnections) {
  auto r = Parse(
      "module sub(input a, input b, output c);\n"
      "endmodule\n"
      "module m;\n"
      "  logic a, b, c;\n"
      "  sub u1(.*);\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
}

TEST(ParserA10, DotStarWithNamedPorts) {
  auto r = Parse(
      "module sub(input a, input b, output c);\n"
      "endmodule\n"
      "module m;\n"
      "  logic a, b, c, d;\n"
      "  sub u1(.a(d), .*);\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
}

// §A.10 clarification 36: parentheses required for comma-separated
// event expressions as actual arguments

TEST(ParserA10, EventExprInParensOk) {
  EXPECT_TRUE(
      ParseOk("module m;\n"
              "  event e1, e2;\n"
              "  initial @(e1 or e2) $display(\"ok\");\n"
              "endmodule\n"));
}

// §A.10 clarification 40: {} denotes empty unpacked array concatenation

TEST(ParserA10, EmptyUnpackedArrayConcat) {
  EXPECT_TRUE(
      ParseOk("module m;\n"
              "  int q[$];\n"
              "  initial q = {};\n"
              "endmodule\n"));
}

// §A.10 clarification 42: omitting parentheses in tf_call

TEST(ParserA10, TaskCallWithoutParens) {
  EXPECT_TRUE(
      ParseOk("module m;\n"
              "  task my_task; endtask\n"
              "  initial my_task;\n"
              "endmodule\n"));
}

TEST(ParserA10, VoidFunctionCallWithParens) {
  EXPECT_TRUE(
      ParseOk("module m;\n"
              "  function void my_func(); endfunction\n"
              "  initial my_func();\n"
              "endmodule\n"));
}

// §A.10 clarification 47: $ primary legal only in queue select

TEST(ParserA10, DollarInQueueSelect) {
  EXPECT_TRUE(
      ParseOk("module m;\n"
              "  int q[$];\n"
              "  initial q[$] = 5;\n"
              "endmodule\n"));
}

// §A.10 clarification 7: parameter in class_item is synonym for localparam

TEST(ParserA10, ParameterInClassItem) {
  EXPECT_TRUE(
      ParseOk("class my_class;\n"
              "  parameter int WIDTH = 8;\n"
              "endclass\n"));
}

TEST(ParserA10, LocalparamInClassItem) {
  EXPECT_TRUE(
      ParseOk("class my_class;\n"
              "  localparam int WIDTH = 8;\n"
              "endclass\n"));
}

// §A.10 clarification 9: default keyword at most once in constructor args

TEST(ParserA10, ClassNewWithDefaultArg) {
  EXPECT_TRUE(
      ParseOk("class my_class;\n"
              "  int x;\n"
              "  function new(int a = 0);\n"
              "    x = a;\n"
              "  endfunction\n"
              "endclass\n"));
}

// §A.10 clarification 17: packed keyword required with struct packed dimensions

TEST(ParserA10, StructPackedOk) {
  EXPECT_TRUE(
      ParseOk("module m;\n"
              "  typedef struct packed {\n"
              "    logic [7:0] a;\n"
              "    logic [7:0] b;\n"
              "  } my_t;\n"
              "endmodule\n"));
}

// §A.10 clarification 18: type_reference in net decl needs net type keyword

TEST(ParserA10, TypeRefInNetDecl) {
  EXPECT_TRUE(
      ParseOk("module m;\n"
              "  wire x;\n"
              "  wire type(x) y;\n"
              "endmodule\n"));
}

TEST(ParserA10, TypeRefInVarDeclWithVar) {
  EXPECT_TRUE(
      ParseOk("module m;\n"
              "  int x;\n"
              "  var type(x) y;\n"
              "endmodule\n"));
}

// §A.10 clarification 29: extends on covergroup only within class

TEST(ParserA10, CovergroupInClass) {
  EXPECT_TRUE(
      ParseOk("class my_class;\n"
              "  covergroup cg;\n"
              "    coverpoint x;\n"
              "  endgroup\n"
              "  int x;\n"
              "endclass\n"));
}

}  // namespace
