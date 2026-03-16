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

TEST(ProgramItemsParsing, ProgramItemPortDecl) {
  auto r = Parse(
      "program prg(input logic clk, output logic done);\n"
      "endprogram\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  ASSERT_EQ(r.cu->programs.size(), 1u);
  auto* p = r.cu->programs[0];
  EXPECT_EQ(p->name, "prg");
  EXPECT_EQ(p->ports.size(), 2u);
  EXPECT_EQ(p->ports[0].direction, Direction::kInput);
  EXPECT_EQ(p->ports[1].direction, Direction::kOutput);
}

TEST(ProgramItemsParsing, ProgramModuleOrGenerateItemDecl) {
  auto r = Parse(
      "program prg;\n"
      "  int count;\n"
      "  function void compute(); endfunction\n"
      "  task run(); endtask\n"
      "endprogram\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  ASSERT_EQ(r.cu->programs.size(), 1u);
  auto& items = r.cu->programs[0]->items;
  EXPECT_TRUE(HasItemKindNamed(items, ModuleItemKind::kVarDecl, "count"));
  EXPECT_TRUE(
      HasItemKindNamed(items, ModuleItemKind::kFunctionDecl, "compute"));
  EXPECT_TRUE(HasItemKindNamed(items, ModuleItemKind::kTaskDecl, "run"));
}

TEST(ProgramItemsParsing, ProgramMultipleItemTypes) {
  auto r = Parse(
      "program prg(input logic clk);\n"
      "  timeunit 1ns;\n"
      "  int count;\n"
      "  assign count = 0;\n"
      "  initial begin $display(\"start\"); end\n"
      "  final begin $display(\"end\"); end\n"
      "  assert property (@(posedge clk) count >= 0);\n"
      "  generate int g; endgenerate\n"
      "  $warning(\"check\");\n"
      "endprogram\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  ASSERT_EQ(r.cu->programs.size(), 1u);
  auto& items = r.cu->programs[0]->items;
  EXPECT_TRUE(HasItemOfKind(items, ModuleItemKind::kVarDecl));
  EXPECT_TRUE(HasItemOfKind(items, ModuleItemKind::kContAssign));
  EXPECT_TRUE(HasItemOfKind(items, ModuleItemKind::kInitialBlock));
  EXPECT_TRUE(HasItemOfKind(items, ModuleItemKind::kFinalBlock));
  EXPECT_TRUE(HasItemOfKind(items, ModuleItemKind::kAssertProperty));
  EXPECT_TRUE(HasItemOfKind(items, ModuleItemKind::kElabSystemTask));
}

TEST(ProgramItemsParsing, WithDataDeclarations) {
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

TEST(ProgramItemsParsing, WithClassDefinition) {
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

TEST(ProgramItemsParsing, WithMultipleInitials) {
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

TEST(ProgramItemsParsing, CannotContainAlways) {
  auto r = Parse(
      "program p;\n"
      "  logic clk, d, q;\n"
      "  always @(posedge clk) q <= d;\n"
      "endprogram\n");
  EXPECT_TRUE(r.has_errors);
}

TEST(ProgramItemsParsing, CannotContainAlwaysComb) {
  auto r = Parse(
      "program p;\n"
      "  logic a, b;\n"
      "  always_comb b = a;\n"
      "endprogram\n");
  EXPECT_TRUE(r.has_errors);
}

TEST(ProgramItemsParsing, CannotContainAlwaysFF) {
  auto r = Parse(
      "program p;\n"
      "  logic clk, d, q;\n"
      "  always_ff @(posedge clk) q <= d;\n"
      "endprogram\n");
  EXPECT_TRUE(r.has_errors);
}

TEST(ProgramItemsParsing, CannotContainAlwaysLatch) {
  auto r = Parse(
      "program p;\n"
      "  logic en, d, q;\n"
      "  always_latch if (en) q <= d;\n"
      "endprogram\n");
  EXPECT_TRUE(r.has_errors);
}

TEST(ProgramItemsParsing, CannotContainModuleInst) {
  auto r = Parse(
      "module sub; endmodule\n"
      "program p;\n"
      "  sub u0();\n"
      "endprogram\n");
  EXPECT_TRUE(r.has_errors);
}

TEST(ProgramItemsParsing, CannotContainGateInst) {
  auto r = Parse(
      "program p;\n"
      "  wire a, b, y;\n"
      "  nand g1(y, a, b);\n"
      "endprogram\n");
  EXPECT_TRUE(r.has_errors);
}

TEST(ProgramItemsParsing, CannotContainUdpInst) {
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

// --- Missing tests below ---

TEST(ProgramItemsParsing, EmptyProgramBody) {
  auto r = Parse("program p;\nendprogram\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  ASSERT_EQ(r.cu->programs.size(), 1u);
  EXPECT_TRUE(r.cu->programs[0]->items.empty());
}

TEST(ProgramItemsParsing, BareSemicolonsIgnored) {
  auto r = Parse(
      "program p;\n"
      "  ;\n"
      "  ;\n"
      "  int x;\n"
      "  ;\n"
      "endprogram\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  ASSERT_EQ(r.cu->programs.size(), 1u);
}

TEST(ProgramItemsParsing, AttributeOnContinuousAssign) {
  auto r = Parse(
      "program p;\n"
      "  wire a, b;\n"
      "  (* keep *) assign a = b;\n"
      "endprogram\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  EXPECT_TRUE(HasAttrNamed(r.cu->programs[0]->items, "keep"));
}

TEST(ProgramItemsParsing, AttributeOnInitialConstruct) {
  auto r = Parse(
      "program p;\n"
      "  (* synthesis *) initial begin end\n"
      "endprogram\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  EXPECT_TRUE(
      HasItemOfKind(r.cu->programs[0]->items, ModuleItemKind::kInitialBlock));
  EXPECT_TRUE(HasAttrNamed(r.cu->programs[0]->items, "synthesis"));
}

TEST(ProgramItemsParsing, ElabTaskFatal) {
  auto r = Parse(
      "program p;\n"
      "  $fatal(1, \"fatal\");\n"
      "endprogram\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  EXPECT_TRUE(
      HasItemOfKind(r.cu->programs[0]->items, ModuleItemKind::kElabSystemTask));
}

TEST(ProgramItemsParsing, ElabTaskInfo) {
  auto r = Parse(
      "program p;\n"
      "  $info(\"info\");\n"
      "endprogram\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  EXPECT_TRUE(
      HasItemOfKind(r.cu->programs[0]->items, ModuleItemKind::kElabSystemTask));
}

TEST(ProgramItemsParsing, AssumePropertyInProgram) {
  auto r = Parse(
      "program p;\n"
      "  assume property (@(posedge clk) req |-> ack);\n"
      "endprogram\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  EXPECT_TRUE(HasItemOfKind(r.cu->programs[0]->items,
                            ModuleItemKind::kAssumeProperty));
}

TEST(ProgramItemsParsing, CoverPropertyInProgram) {
  auto r = Parse(
      "program p;\n"
      "  cover property (@(posedge clk) req);\n"
      "endprogram\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  EXPECT_TRUE(HasItemOfKind(r.cu->programs[0]->items,
                            ModuleItemKind::kCoverProperty));
}

TEST(ProgramItemsParsing, GenerateCaseInProgram) {
  auto r = Parse(
      "program p;\n"
      "  parameter int MODE = 1;\n"
      "  case (MODE)\n"
      "    0: begin : m0 int x; end\n"
      "    1: begin : m1 int y; end\n"
      "  endcase\n"
      "endprogram\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  EXPECT_TRUE(HasItemOfKind(r.cu->programs[0]->items,
                            ModuleItemKind::kGenerateCase));
}

TEST(ProgramItemsParsing, TypedefInProgram) {
  auto r = Parse(
      "program p;\n"
      "  typedef logic [7:0] byte_t;\n"
      "endprogram\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  EXPECT_TRUE(
      HasItemOfKind(r.cu->programs[0]->items, ModuleItemKind::kTypedef));
}

TEST(ProgramItemsParsing, ImportDeclInProgram) {
  auto r = Parse(
      "package pkg;\n"
      "  int x;\n"
      "endpackage\n"
      "program p;\n"
      "  import pkg::*;\n"
      "endprogram\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  EXPECT_TRUE(
      HasItemOfKind(r.cu->programs[0]->items, ModuleItemKind::kImportDecl));
}

}  // namespace
