#include "fixture_parser.h"
#include "helpers_parser_verify.h"

using namespace delta;

namespace {

TEST(ProgramItemsParsing, ProgramWithInitial) {
  auto r = Parse(
      "program test_prg;\n"
      "  initial begin\n"
      "    $display(\"hello\");\n"
      "  end\n"
      "endprogram\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  ASSERT_EQ(r.cu->programs.size(), 1u);
  EXPECT_TRUE(
      HasItemOfKind(r.cu->programs[0]->items, ModuleItemKind::kInitialBlock));
}

TEST(ProgramItemsParsing, ProgramContinuousAssign) {
  auto r = Parse(
      "program test_prg;\n"
      "  wire a, y;\n"
      "  assign y = a;\n"
      "endprogram\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  EXPECT_TRUE(
      HasItemOfKind(r.cu->programs[0]->items, ModuleItemKind::kContAssign));
}

TEST(ProgramItemsParsing, ProgramFinal) {
  auto r = Parse(
      "program test_prg;\n"
      "  final $display(\"done\");\n"
      "endprogram\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  EXPECT_TRUE(
      HasItemOfKind(r.cu->programs[0]->items, ModuleItemKind::kFinalBlock));
}

TEST(ProgramItemsParsing, ProgramFunctionDecl) {
  auto r = Parse(
      "program test_prg;\n"
      "  function int add(int a, int b);\n"
      "    return a + b;\n"
      "  endfunction\n"
      "endprogram\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  EXPECT_TRUE(
      HasItemOfKind(r.cu->programs[0]->items, ModuleItemKind::kFunctionDecl));
}

TEST(ProgramItemsParsing, ProgramTaskDecl) {
  auto r = Parse(
      "program test_prg;\n"
      "  task run();\n"
      "    $display(\"run\");\n"
      "  endtask\n"
      "endprogram\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  EXPECT_TRUE(
      HasItemOfKind(r.cu->programs[0]->items, ModuleItemKind::kTaskDecl));
}

TEST(ProgramItemsParsing, ProgramTimeunits) {
  auto r = Parse(
      "program test_prg;\n"
      "  timeunit 1ns;\n"
      "  timeprecision 1ps;\n"
      "endprogram\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
}

TEST(ProgramItemsParsing, ProgramGenFor) {
  auto r = Parse(
      "program test_prg;\n"
      "  genvar i;\n"
      "  for (i = 0; i < 4; i = i + 1) begin : gen\n"
      "    wire w;\n"
      "  end\n"
      "endprogram\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  EXPECT_TRUE(
      HasItemOfKind(r.cu->programs[0]->items, ModuleItemKind::kGenerateFor));
}

TEST(ProgramItemsParsing, ProgramGenIf) {
  auto r = Parse(
      "program test_prg;\n"
      "  if (1) begin : blk\n"
      "    wire w;\n"
      "  end\n"
      "endprogram\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  EXPECT_TRUE(
      HasItemOfKind(r.cu->programs[0]->items, ModuleItemKind::kGenerateIf));
}

TEST(ProgramItemsParsing, ProgramElabTask) {
  auto r = Parse(
      "program test_prg;\n"
      "  $error(\"test error\");\n"
      "endprogram\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
}

TEST(ProgramItemsParsing, ProgramAnsiPorts) {
  auto r = Parse(
      "program test_prg(input logic clk, input logic rst);\n"
      "  initial begin end\n"
      "endprogram\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  EXPECT_EQ(r.cu->programs[0]->ports.size(), 2u);
}

TEST(ProgramItemsParsing, ProgramConcurrentAssert) {
  auto r = Parse(
      "program test_prg;\n"
      "  assert property (@(posedge clk) a |-> b);\n"
      "endprogram\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
}

TEST(ProgramItemsParsing, ProgramGenerateRegion) {
  auto r = Parse(
      "program test_prg;\n"
      "  generate\n"
      "    wire w;\n"
      "  endgenerate\n"
      "endprogram\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
}

TEST(ProgramItemsParsing, ProgramClocking) {
  auto r = Parse(
      "program test_prg;\n"
      "  clocking cb @(posedge clk);\n"
      "  endclocking\n"
      "endprogram\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
}

}  // namespace
