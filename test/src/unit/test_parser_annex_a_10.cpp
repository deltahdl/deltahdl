#include "fixture_parser.h"

using namespace delta;

namespace {

TEST(TopLevelGrammarParsing, ImportInHeaderFollowedByPorts) {
  auto r = Parse(
      "module m import pkg::*; (input a, output b);\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  EXPECT_EQ(r.cu->modules[0]->ports.size(), 2u);
}

TEST(TopLevelGrammarParsing, ImportInHeaderFollowedByParams) {
  auto r = Parse(
      "module m import pkg::*; #(parameter int W = 8) (input a);\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
}

TEST(TopLevelGrammarParsing, ImportInHeaderFollowedByBoth) {
  auto r = Parse(
      "module m import pkg::*; #(parameter int W = 8) (input a, output b);\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
}

TEST(TopLevelGrammarParsing, AutomaticInProceduralBlockOk) {
  EXPECT_TRUE(
      ParseOk("module m;\n"
              "  initial begin\n"
              "    automatic int x = 5;\n"
              "  end\n"
              "endmodule\n"));
}

TEST(TopLevelGrammarParsing, MatchesPrecedenceOverLogicalAnd) {
  EXPECT_TRUE(
      ParseOk("module m;\n"
              "  initial begin\n"
              "    if (x matches 1 && y matches 2)\n"
              "      $display(\"ok\");\n"
              "  end\n"
              "endmodule\n"));
}

TEST(TopLevelGrammarParsing, DotStarOnceInPortConnections) {
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

TEST(TopLevelGrammarParsing, DotStarWithNamedPorts) {
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

TEST(TopLevelGrammarParsing, EventExprInParensOk) {
  EXPECT_TRUE(
      ParseOk("module m;\n"
              "  event e1, e2;\n"
              "  initial @(e1 or e2) $display(\"ok\");\n"
              "endmodule\n"));
}

TEST(TopLevelGrammarParsing, EmptyUnpackedArrayConcat) {
  EXPECT_TRUE(
      ParseOk("module m;\n"
              "  int q[$];\n"
              "  initial q = {};\n"
              "endmodule\n"));
}

TEST(TopLevelGrammarParsing, TaskCallWithoutParens) {
  EXPECT_TRUE(
      ParseOk("module m;\n"
              "  task my_task; endtask\n"
              "  initial my_task;\n"
              "endmodule\n"));
}

TEST(TopLevelGrammarParsing, VoidFunctionCallWithParens) {
  EXPECT_TRUE(
      ParseOk("module m;\n"
              "  function void my_func(); endfunction\n"
              "  initial my_func();\n"
              "endmodule\n"));
}

TEST(TopLevelGrammarParsing, DollarInQueueSelect) {
  EXPECT_TRUE(
      ParseOk("module m;\n"
              "  int q[$];\n"
              "  initial q[$] = 5;\n"
              "endmodule\n"));
}

TEST(TopLevelGrammarParsing, ParameterInClassItem) {
  EXPECT_TRUE(
      ParseOk("class my_class;\n"
              "  parameter int WIDTH = 8;\n"
              "endclass\n"));
}

TEST(TopLevelGrammarParsing, LocalparamInClassItem) {
  EXPECT_TRUE(
      ParseOk("class my_class;\n"
              "  localparam int WIDTH = 8;\n"
              "endclass\n"));
}

TEST(TopLevelGrammarParsing, ClassNewWithDefaultArg) {
  EXPECT_TRUE(
      ParseOk("class my_class;\n"
              "  int x;\n"
              "  function new(int a = 0);\n"
              "    x = a;\n"
              "  endfunction\n"
              "endclass\n"));
}

TEST(TopLevelGrammarParsing, StructPackedOk) {
  EXPECT_TRUE(
      ParseOk("module m;\n"
              "  typedef struct packed {\n"
              "    logic [7:0] a;\n"
              "    logic [7:0] b;\n"
              "  } my_t;\n"
              "endmodule\n"));
}

TEST(TopLevelGrammarParsing, TypeRefInNetDecl) {
  EXPECT_TRUE(
      ParseOk("module m;\n"
              "  wire x;\n"
              "  wire type(x) y;\n"
              "endmodule\n"));
}

TEST(TopLevelGrammarParsing, TypeRefInVarDeclWithVar) {
  EXPECT_TRUE(
      ParseOk("module m;\n"
              "  int x;\n"
              "  var type(x) y;\n"
              "endmodule\n"));
}

TEST(TopLevelGrammarParsing, CovergroupInClass) {
  EXPECT_TRUE(
      ParseOk("class my_class;\n"
              "  covergroup cg;\n"
              "    coverpoint x;\n"
              "  endgroup\n"
              "  int x;\n"
              "endclass\n"));
}

}  // namespace
