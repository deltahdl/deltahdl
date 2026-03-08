#include "fixture_parser.h"
#include "helpers_parser_verify.h"

using namespace delta;

namespace {

TEST(ParserClause03, Cl3_4_ProgramEnclosedByKeywords) {
  auto r = Parse("program p; endprogram");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  ASSERT_EQ(r.cu->programs.size(), 1u);
  EXPECT_EQ(r.cu->programs[0]->name, "p");
  EXPECT_EQ(r.cu->programs[0]->decl_kind, ModuleDeclKind::kProgram);
}

TEST(ParserClause03, Cl3_4_ProgramWithDataDeclarations) {
  auto r = Parse(
      "program p;\n"
      "  logic [7:0] count;\n"
      "  int status;\n"
      "  byte b;\n"
      "endprogram\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  EXPECT_GE(r.cu->programs[0]->items.size(), 3u);
}

TEST(ParserClause03, Cl3_4_ProgramWithClassDefinition) {
  auto r = Parse(
      "program p;\n"
      "  class my_trans;\n"
      "    int data;\n"
      "  endclass\n"
      "endprogram\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  EXPECT_TRUE(
      HasItemOfKind(r.cu->programs[0]->items, ModuleItemKind::kClassDecl));
}

TEST(ParserClause03, Cl3_4_ProgramWithFunction) {
  auto r = Parse(
      "program p;\n"
      "  function int add(int a, int b);\n"
      "    return a + b;\n"
      "  endfunction\n"
      "endprogram\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  EXPECT_TRUE(
      HasItemOfKind(r.cu->programs[0]->items, ModuleItemKind::kFunctionDecl));
}

TEST(ParserClause03, Cl3_4_ProgramWithTask) {
  auto r = Parse(
      "program p;\n"
      "  task do_work;\n"
      "  endtask\n"
      "endprogram\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  EXPECT_TRUE(
      HasItemOfKind(r.cu->programs[0]->items, ModuleItemKind::kTaskDecl));
}

TEST(ParserClause03, Cl3_4_ProgramWithInitialBlock) {
  auto r = Parse(
      "program p;\n"
      "  initial begin\n"
      "    $display(\"test\");\n"
      "  end\n"
      "endprogram\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  EXPECT_TRUE(
      HasItemOfKind(r.cu->programs[0]->items, ModuleItemKind::kInitialBlock));
}

TEST(ParserClause03, Cl3_4_ProgramWithFinalBlock) {
  auto r = Parse(
      "program p;\n"
      "  final $display(\"done\");\n"
      "endprogram\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  EXPECT_TRUE(
      HasItemOfKind(r.cu->programs[0]->items, ModuleItemKind::kFinalBlock));
}

TEST(ParserClause03, Cl3_4_ProgramWithMultipleInitials) {
  auto r = Parse(
      "program p;\n"
      "  initial $display(\"a\");\n"
      "  initial $display(\"b\");\n"
      "endprogram\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  EXPECT_EQ(
      CountItemsByKind(r.cu->programs[0]->items, ModuleItemKind::kInitialBlock),
      2u);
}

TEST(ParserClause03, Cl3_4_ProgramCannotContainAlways) {
  auto r = Parse(
      "program p;\n"
      "  logic clk, d, q;\n"
      "  always @(posedge clk) q <= d;\n"
      "endprogram\n");
  EXPECT_TRUE(r.has_errors);
}

TEST(ParserClause03, Cl3_4_ProgramCannotContainAlwaysComb) {
  auto r = Parse(
      "program p;\n"
      "  logic a, b;\n"
      "  always_comb b = a;\n"
      "endprogram\n");
  EXPECT_TRUE(r.has_errors);
}

TEST(ParserClause03, Cl3_4_ProgramCannotContainAlwaysFF) {
  auto r = Parse(
      "program p;\n"
      "  logic clk, d, q;\n"
      "  always_ff @(posedge clk) q <= d;\n"
      "endprogram\n");
  EXPECT_TRUE(r.has_errors);
}

TEST(ParserClause03, Cl3_4_ProgramCannotContainAlwaysLatch) {
  auto r = Parse(
      "program p;\n"
      "  logic en, d, q;\n"
      "  always_latch if (en) q <= d;\n"
      "endprogram\n");
  EXPECT_TRUE(r.has_errors);
}

TEST(ParserClause03, Cl3_4_ProgramCannotContainModuleInst) {
  auto r = Parse(
      "module sub; endmodule\n"
      "program p;\n"
      "  sub u0();\n"
      "endprogram\n");
  EXPECT_TRUE(r.has_errors);
}

TEST(ParserClause03, Cl3_4_ProgramCannotContainGateInst) {
  auto r = Parse(
      "program p;\n"
      "  wire a, b, y;\n"
      "  nand g1(y, a, b);\n"
      "endprogram\n");
  EXPECT_TRUE(r.has_errors);
}

TEST(ParserClause03, Cl3_4_ProgramCannotContainUdpInst) {
  auto r = Parse(
      "primitive udp_buf (output out, input in);\n"
      "  table 0 : 0; 1 : 1; endtable\n"
      "endprimitive\n"
      "program p;\n"
      "  wire a, b;\n"
      "  udp_buf u1(a, b);\n"
      "endprogram\n");
  EXPECT_TRUE(r.has_errors);
}

TEST(ParserClause03, Cl3_4_ProgramWithPorts) {
  auto r = Parse(
      "program p(input clk, input [16:1] addr, inout [7:0] data);\n"
      "endprogram\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  EXPECT_EQ(r.cu->programs[0]->ports.size(), 3u);
}

TEST(ParserClause03, Cl3_4_SampleProgramDeclaration) {
  auto r = Parse(
      "program test (input clk, input [16:1] addr, inout [7:0] data);\n"
      "  initial begin\n"
      "  end\n"
      "endprogram\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  ASSERT_EQ(r.cu->programs.size(), 1u);
  EXPECT_EQ(r.cu->programs[0]->name, "test");
  EXPECT_EQ(r.cu->programs[0]->ports.size(), 3u);
  EXPECT_TRUE(
      HasItemOfKind(r.cu->programs[0]->items, ModuleItemKind::kInitialBlock));
}

}
