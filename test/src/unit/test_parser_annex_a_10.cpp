#include "fixture_parser.h"

using namespace delta;

namespace {

TEST(BnfClarificationParsing, ImportInHeaderFollowedByPorts) {
  auto r = Parse(
      "module m import pkg::*; (input a, output b);\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  EXPECT_EQ(r.cu->modules[0]->ports.size(), 2u);
}

TEST(BnfClarificationParsing, ImportInHeaderFollowedByParams) {
  auto r = Parse(
      "module m import pkg::*; #(parameter int W = 8) (input a);\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
}

TEST(BnfClarificationParsing, ImportInHeaderFollowedByBoth) {
  auto r = Parse(
      "module m import pkg::*; #(parameter int W = 8) (input a, output b);\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
}

TEST(BnfClarificationParsing, AutomaticInProceduralBlockOk) {
  EXPECT_TRUE(
      ParseOk("module m;\n"
              "  initial begin\n"
              "    automatic int x = 5;\n"
              "  end\n"
              "endmodule\n"));
}

TEST(BnfClarificationParsing, MatchesPrecedenceOverLogicalAnd) {
  EXPECT_TRUE(
      ParseOk("module m;\n"
              "  initial begin\n"
              "    if (x matches 1 && y matches 2)\n"
              "      $display(\"ok\");\n"
              "  end\n"
              "endmodule\n"));
}

TEST(BnfClarificationParsing, DotStarOnceInPortConnections) {
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

TEST(BnfClarificationParsing, DotStarWithNamedPorts) {
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

TEST(BnfClarificationParsing, EventExprInParensOk) {
  EXPECT_TRUE(
      ParseOk("module m;\n"
              "  event e1, e2;\n"
              "  initial @(e1 or e2) $display(\"ok\");\n"
              "endmodule\n"));
}

TEST(BnfClarificationParsing, EmptyUnpackedArrayConcat) {
  EXPECT_TRUE(
      ParseOk("module m;\n"
              "  int q[$];\n"
              "  initial q = {};\n"
              "endmodule\n"));
}

TEST(BnfClarificationParsing, TaskCallWithoutParens) {
  EXPECT_TRUE(
      ParseOk("module m;\n"
              "  task my_task; endtask\n"
              "  initial my_task;\n"
              "endmodule\n"));
}

TEST(BnfClarificationParsing, VoidFunctionCallWithParens) {
  EXPECT_TRUE(
      ParseOk("module m;\n"
              "  function void my_func(); endfunction\n"
              "  initial my_func();\n"
              "endmodule\n"));
}

TEST(BnfClarificationParsing, DollarInQueueSelect) {
  EXPECT_TRUE(
      ParseOk("module m;\n"
              "  int q[$];\n"
              "  initial q[$] = 5;\n"
              "endmodule\n"));
}

TEST(BnfClarificationParsing, StructPackedOk) {
  EXPECT_TRUE(
      ParseOk("module m;\n"
              "  typedef struct packed {\n"
              "    logic [7:0] a;\n"
              "    logic [7:0] b;\n"
              "  } my_t;\n"
              "endmodule\n"));
}

TEST(BnfClarificationParsing, TypeRefInNetDecl) {
  EXPECT_TRUE(
      ParseOk("module m;\n"
              "  wire x;\n"
              "  wire type(x) y;\n"
              "endmodule\n"));
}

TEST(BnfClarificationParsing, TypeRefInVarDeclWithVar) {
  EXPECT_TRUE(
      ParseOk("module m;\n"
              "  int x;\n"
              "  var type(x) y;\n"
              "endmodule\n"));
}

// Item 10: rand/randc mutual exclusion

TEST(BnfClarificationParsing, ErrorRandAndRandc) {
  auto r = Parse(
      "class c;\n"
      "  rand randc int x;\n"
      "endclass\n");
  EXPECT_TRUE(r.has_errors);
}

TEST(BnfClarificationParsing, ErrorDuplicateRand) {
  auto r = Parse(
      "class c;\n"
      "  rand rand int x;\n"
      "endclass\n");
  EXPECT_TRUE(r.has_errors);
}

// Item 10: static/virtual duplicate

TEST(BnfClarificationParsing, ErrorDuplicateStatic) {
  auto r = Parse(
      "class c;\n"
      "  static static int x;\n"
      "endclass\n");
  EXPECT_TRUE(r.has_errors);
}

// Item 17: union with packed keyword

TEST(BnfClarificationParsing, UnionPackedOk) {
  EXPECT_TRUE(
      ParseOk("module m;\n"
              "  typedef union packed {\n"
              "    logic [7:0] a;\n"
              "    logic [7:0] b;\n"
              "  } my_t;\n"
              "endmodule\n"));
}

// Item 42: nonvoid function call requires parens

TEST(BnfClarificationParsing, NonvoidFunctionCallWithParens) {
  EXPECT_TRUE(
      ParseOk("module m;\n"
              "  function int my_func(); return 0; endfunction\n"
              "  int y;\n"
              "  initial y = my_func();\n"
              "endmodule\n"));
}

// Item 52: streaming concatenation basic forms

TEST(BnfClarificationParsing, StreamingConcatRight) {
  EXPECT_TRUE(
      ParseOk("module m;\n"
              "  logic [31:0] x;\n"
              "  logic [31:0] y;\n"
              "  assign y = {>>{ x }};\n"
              "endmodule\n"));
}

TEST(BnfClarificationParsing, StreamingConcatLeft) {
  EXPECT_TRUE(
      ParseOk("module m;\n"
              "  logic [31:0] x;\n"
              "  logic [31:0] y;\n"
              "  assign y = {<<{ x }};\n"
              "endmodule\n"));
}

TEST(BnfClarificationParsing, StreamingConcatWithSliceSize) {
  EXPECT_TRUE(
      ParseOk("module m;\n"
              "  logic [31:0] x;\n"
              "  logic [31:0] y;\n"
              "  assign y = {<<8{ x }};\n"
              "endmodule\n"));
}

// Item 29: covergroup extends only within class

TEST(BnfClarificationParsing, CovergroupExtendsInClassOk) {
  EXPECT_TRUE(
      ParseOk("class c;\n"
              "  int val;\n"
              "  covergroup base_cg;\n"
              "    coverpoint val;\n"
              "  endgroup\n"
              "endclass\n"));
}

// Item 8: pure virtual method parses ok (constraint enforced at elaboration)

TEST(BnfClarificationParsing, PureVirtualMethodOk) {
  EXPECT_TRUE(
      ParseOk("virtual class c;\n"
              "  pure virtual function void do_it();\n"
              "endclass\n"));
}

}  // namespace
