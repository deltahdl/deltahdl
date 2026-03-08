#include "fixture_parser.h"
#include "helpers_parser_verify.h"

using namespace delta;

namespace {

// §A.1.7 Program items

// program_item ::= port_declaration ; | non_port_program_item

TEST(ProgramItemsA17, ProgramWithInitial) {
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

// non_port_program_item ::= continuous_assign
TEST(ProgramItemsA17, ProgramContinuousAssign) {
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

// non_port_program_item ::= final_construct
TEST(ProgramItemsA17, ProgramFinal) {
  auto r = Parse(
      "program test_prg;\n"
      "  final $display(\"done\");\n"
      "endprogram\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  EXPECT_TRUE(
      HasItemOfKind(r.cu->programs[0]->items, ModuleItemKind::kFinalBlock));
}

// non_port_program_item ::= module_or_generate_item_declaration
TEST(ProgramItemsA17, ProgramFunctionDecl) {
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

TEST(ProgramItemsA17, ProgramTaskDecl) {
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

// non_port_program_item ::= timeunits_declaration
TEST(ProgramItemsA17, ProgramTimeunits) {
  auto r = Parse(
      "program test_prg;\n"
      "  timeunit 1ns;\n"
      "  timeprecision 1ps;\n"
      "endprogram\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
}

// program_generate_item ::= loop_generate_construct
TEST(ProgramItemsA17, ProgramGenFor) {
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

// program_generate_item ::= conditional_generate_construct
TEST(ProgramItemsA17, ProgramGenIf) {
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

// program_generate_item ::= elaboration_severity_system_task
TEST(ProgramItemsA17, ProgramElabTask) {
  auto r = Parse(
      "program test_prg;\n"
      "  $error(\"test error\");\n"
      "endprogram\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
}

// program with ANSI ports
TEST(ProgramItemsA17, ProgramAnsiPorts) {
  auto r = Parse(
      "program test_prg(input logic clk, input logic rst);\n"
      "  initial begin end\n"
      "endprogram\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  EXPECT_EQ(r.cu->programs[0]->ports.size(), 2u);
}

// concurrent_assertion_item
TEST(ProgramItemsA17, ProgramConcurrentAssert) {
  auto r = Parse(
      "program test_prg;\n"
      "  assert property (@(posedge clk) a |-> b);\n"
      "endprogram\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
}

// program_generate_item ::= generate_region
TEST(ProgramItemsA17, ProgramGenerateRegion) {
  auto r = Parse(
      "program test_prg;\n"
      "  generate\n"
      "    wire w;\n"
      "  endgenerate\n"
      "endprogram\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
}

// clocking_declaration inside program
TEST(ProgramItemsA17, ProgramClocking) {
  auto r = Parse(
      "program test_prg;\n"
      "  clocking cb @(posedge clk);\n"
      "  endclocking\n"
      "endprogram\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
}

}  // namespace
