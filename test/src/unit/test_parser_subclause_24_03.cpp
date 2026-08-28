#include "fixture_parser.h"
#include "fixture_program.h"
#include "helpers_parser_verify.h"
#include "helpers_reported_error.h"

using namespace delta;

namespace {

TEST_F(ProgramTestParse, ProgramAutomaticLifetime) {
  auto* unit = Parse("program automatic auto_prog; endprogram");
  ASSERT_EQ(unit->programs.size(), 1u);
  EXPECT_EQ(unit->programs[0]->name, "auto_prog");
  EXPECT_EQ(unit->programs[0]->decl_kind, ModuleDeclKind::kProgram);
}

TEST_F(ProgramTestParse, ProgramStaticLifetime) {
  auto* unit = Parse("program static static_prog; endprogram");
  ASSERT_EQ(unit->programs.size(), 1u);
  EXPECT_EQ(unit->programs[0]->name, "static_prog");
  EXPECT_EQ(unit->programs[0]->decl_kind, ModuleDeclKind::kProgram);
  EXPECT_FALSE(unit->programs[0]->is_automatic);
}

TEST_F(ProgramTestParse, MultipleProgramsCoexist) {
  auto* unit = Parse(
      "program p1; endprogram\n"
      "program p2; endprogram\n"
      "module m; endmodule\n");
  EXPECT_EQ(unit->programs.size(), 2u);
  EXPECT_EQ(unit->modules.size(), 1u);
  EXPECT_EQ(unit->programs[0]->name, "p1");
  EXPECT_EQ(unit->programs[1]->name, "p2");
}

TEST_F(ProgramParseTest, ProgramWithEndLabel) {
  auto* unit = Parse("program p; endprogram : p");
  ASSERT_EQ(unit->programs.size(), 1u);
  EXPECT_EQ(unit->programs[0]->name, "p");
  EXPECT_EQ(unit->programs[0]->decl_kind, ModuleDeclKind::kProgram);
}

TEST_F(ProgramParseTest, ProgramWithPorts) {
  auto* unit = Parse(
      "program p(input logic clk, input logic rst);\n"
      "endprogram\n");
  ASSERT_EQ(unit->programs.size(), 1u);
  EXPECT_EQ(unit->programs[0]->name, "p");
  EXPECT_EQ(unit->programs[0]->decl_kind, ModuleDeclKind::kProgram);
  ASSERT_GE(unit->programs[0]->ports.size(), 2u);
  EXPECT_EQ(unit->programs[0]->ports[0].name, "clk");
  EXPECT_EQ(unit->programs[0]->ports[0].direction, Direction::kInput);
  EXPECT_EQ(unit->programs[0]->ports[1].name, "rst");
  EXPECT_EQ(unit->programs[0]->ports[1].direction, Direction::kInput);
}

TEST_F(ProgramParseTest, ProgramWithParameters) {
  auto* unit = Parse(
      "program p #(parameter N = 8)(input logic clk);\n"
      "endprogram\n");
  ASSERT_EQ(unit->programs.size(), 1u);
  EXPECT_EQ(unit->programs[0]->name, "p");
  EXPECT_EQ(unit->programs[0]->decl_kind, ModuleDeclKind::kProgram);
  ASSERT_EQ(unit->programs[0]->params.size(), 1u);
  EXPECT_EQ(unit->programs[0]->params[0].first, "N");
  ASSERT_GE(unit->programs[0]->ports.size(), 1u);
  EXPECT_EQ(unit->programs[0]->ports[0].name, "clk");
}

TEST_F(ProgramParseTest, ProgramWithMultipleItems) {
  auto* unit = Parse(
      "program p;\n"
      "  logic [7:0] data;\n"
      "  assign data = 8'hFF;\n"
      "  initial begin\n"
      "    $display(\"test\");\n"
      "  end\n"
      "endprogram\n");
  ASSERT_EQ(unit->programs.size(), 1u);
  EXPECT_EQ(unit->programs[0]->name, "p");
  EXPECT_EQ(unit->programs[0]->decl_kind, ModuleDeclKind::kProgram);
  ASSERT_GE(unit->programs[0]->items.size(), 3u);
}

TEST(ProgramDeclaration, WildcardPorts) {
  auto r = Parse("program prg(.*); endprogram\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  ASSERT_EQ(r.cu->programs.size(), 1u);
  EXPECT_TRUE(r.cu->programs[0]->has_wildcard_ports);
}

TEST(ProgramDeclaration, ExternProgram) {
  auto r = Parse("extern program prg(input logic clk);\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  ASSERT_EQ(r.cu->programs.size(), 1u);
  EXPECT_TRUE(r.cu->programs[0]->is_extern);
  EXPECT_EQ(r.cu->programs[0]->name, "prg");
}

TEST(ProgramDeclaration, NonAnsiHeader) {
  auto r = Parse(
      "program prg(clk);\n"
      "  input clk;\n"
      "endprogram\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  ASSERT_EQ(r.cu->programs.size(), 1u);
  EXPECT_EQ(r.cu->programs[0]->ports.size(), 1u);
}

TEST(ProgramDeclaration, ExternProgramNonAnsiHeader) {
  auto r = Parse("extern program prg(clk, rst);\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  ASSERT_EQ(r.cu->programs.size(), 1u);
  EXPECT_TRUE(r.cu->programs[0]->is_extern);
}

TEST(ProgramDeclaration, NestedProgramInModule) {
  auto r = Parse(
      "module top;\n"
      "  program p;\n"
      "    initial $display(\"p\");\n"
      "  endprogram\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  ASSERT_EQ(r.cu->modules.size(), 1u);
  EXPECT_TRUE(HasItemOfKind(r.cu->modules[0]->items,
                            ModuleItemKind::kNestedModuleDecl));
}

TEST(ProgramDeclaration, MultipleNestedProgramsInModule) {
  auto r = Parse(
      "module test;\n"
      "  int shared;\n"
      "  program p1;\n"
      "  endprogram\n"
      "  program p2;\n"
      "  endprogram\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  ASSERT_EQ(r.cu->modules.size(), 1u);
  EXPECT_EQ(CountItemsByKind(r.cu->modules[0]->items,
                             ModuleItemKind::kNestedModuleDecl),
            2u);
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

TEST(ProgramItemsParsing, ProgramTimeunits) {
  auto r = Parse(
      "program test_prg;\n"
      "  timeunit 1ns;\n"
      "  timeprecision 1ps;\n"
      "endprogram\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
}

TEST(ProgramItemsParsing, ProgramTimeunitAfterOtherItemRejected) {
  auto r = Parse(
      "program test_prg;\n"
      "  int x;\n"
      "  timeunit 1ns;\n"
      "endprogram\n");
  // §3.14.2.2 owns the placement rule for a later timeunit, so
  // ValidateTimeScopeAfterParse in src/parser/parser_items.cpp files the report
  // there rather than §24.3.
  EXPECT_TRUE(ReportedError(r.diags,
                            "timeunit as a later item requires a matching "
                            "prior declaration in the same time scope",
                            3, "3.14.2.2"));
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
  EXPECT_TRUE(
      HasItemOfKind(r.cu->programs[0]->items, ModuleItemKind::kAssumeProperty));
}

TEST(ProgramItemsParsing, CoverPropertyInProgram) {
  auto r = Parse(
      "program p;\n"
      "  cover property (@(posedge clk) req);\n"
      "endprogram\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  EXPECT_TRUE(
      HasItemOfKind(r.cu->programs[0]->items, ModuleItemKind::kCoverProperty));
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
  EXPECT_TRUE(
      HasItemOfKind(r.cu->programs[0]->items, ModuleItemKind::kGenerateCase));
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

TEST(ProgramItemsParsing, CannotContainNestedModuleDecl) {
  auto r = Parse(
      "program p;\n"
      "  module inner; endmodule\n"
      "endprogram\n");
  EXPECT_TRUE(ReportedError(
      r.diags, "module declarations not allowed in programs", 2, "24.3"));
}

TEST(ProgramItemsParsing, CannotContainNestedInterfaceDecl) {
  auto r = Parse(
      "program p;\n"
      "  interface inner; endinterface\n"
      "endprogram\n");
  EXPECT_TRUE(ReportedError(
      r.diags, "interface declarations not allowed in programs", 2, "24.3"));
}

TEST(ProgramItemsParsing, CannotContainNestedProgramDecl) {
  auto r = Parse(
      "program p;\n"
      "  program inner; endprogram\n"
      "endprogram\n");
  EXPECT_TRUE(ReportedError(
      r.diags, "program declarations not allowed in programs", 2, "24.3"));
}

TEST(ProgramItemsParsing, GenerateRegionCannotContainAlways) {
  auto r = Parse(
      "program p;\n"
      "  logic clk, d, q;\n"
      "  generate\n"
      "    always @(posedge clk) q <= d;\n"
      "  endgenerate\n"
      "endprogram\n");
  EXPECT_TRUE(ReportedError(
      r.diags, "always procedures not allowed in programs", 4, "24.3"));
}

TEST(ProgramItemsParsing, LoopGenerateCannotContainAlways) {
  auto r = Parse(
      "program p;\n"
      "  genvar i;\n"
      "  for (i = 0; i < 2; i = i + 1) begin : gen\n"
      "    always @* begin end\n"
      "  end\n"
      "endprogram\n");
  EXPECT_TRUE(ReportedError(
      r.diags, "always procedures not allowed in programs", 4, "24.3"));
}

TEST(ProgramItemsParsing, ConditionalGenerateCannotContainModuleInst) {
  auto r = Parse(
      "module sub; endmodule\n"
      "program p;\n"
      "  if (1) begin : gen\n"
      "    sub u0();\n"
      "  end\n"
      "endprogram\n");
  EXPECT_TRUE(ReportedError(r.diags, "instantiations not allowed in programs",
                            4, "24.3"));
}

static int CountItemsOfKind(const std::vector<ModuleItem*>& items,
                            ModuleItemKind kind) {
  int count = 0;
  for (const auto* item : items) {
    if (item->kind == kind) ++count;
  }
  return count;
}

TEST_F(ProgramTestParse, ProgramWithMultipleInitialBlocks) {
  auto* unit = Parse(
      "program p;\n"
      "  initial $display(\"init1\");\n"
      "  initial $display(\"init2\");\n"
      "endprogram\n");
  ASSERT_EQ(unit->programs.size(), 1u);
  EXPECT_EQ(
      CountItemsOfKind(unit->programs[0]->items, ModuleItemKind::kInitialBlock),
      2);
}

TEST_F(ProgramTestParse, ProgramWithVariableDecls) {
  auto* unit = Parse(
      "program p;\n"
      "  logic [31:0] data;\n"
      "  logic [7:0] addr;\n"
      "endprogram\n");
  ASSERT_EQ(unit->programs.size(), 1u);
  EXPECT_GE(unit->programs[0]->items.size(), 2u);
}

TEST_F(ProgramParseTest, EmptyProgram) {
  auto* unit = Parse("program p; endprogram");
  ASSERT_EQ(unit->programs.size(), 1u);
  EXPECT_EQ(unit->programs[0]->name, "p");
  EXPECT_EQ(unit->programs[0]->decl_kind, ModuleDeclKind::kProgram);
  EXPECT_TRUE(unit->programs[0]->ports.empty());
  EXPECT_TRUE(unit->programs[0]->params.empty());
  EXPECT_TRUE(unit->programs[0]->items.empty());
}

TEST_F(ProgramParseTest, ProgramWithInitialBlock) {
  auto* unit = Parse(
      "program p;\n"
      "  initial begin\n"
      "    $display(\"hello\");\n"
      "  end\n"
      "endprogram\n");
  ASSERT_EQ(unit->programs.size(), 1u);
  EXPECT_EQ(unit->programs[0]->name, "p");
  EXPECT_EQ(unit->programs[0]->decl_kind, ModuleDeclKind::kProgram);
  ASSERT_EQ(unit->programs[0]->items.size(), 1u);
  EXPECT_EQ(unit->programs[0]->items[0]->kind, ModuleItemKind::kInitialBlock);
}

TEST_F(ProgramParseTest, ProgramWithTaskDecl) {
  auto* unit = Parse(
      "program p;\n"
      "  task run;\n"
      "    $display(\"running\");\n"
      "  endtask\n"
      "endprogram\n");
  ASSERT_EQ(unit->programs.size(), 1u);
  EXPECT_EQ(unit->programs[0]->name, "p");
  EXPECT_EQ(unit->programs[0]->decl_kind, ModuleDeclKind::kProgram);
  ASSERT_GE(unit->programs[0]->items.size(), 1u);
  EXPECT_EQ(unit->programs[0]->items[0]->kind, ModuleItemKind::kTaskDecl);
  EXPECT_EQ(unit->programs[0]->items[0]->name, "run");
}

TEST_F(ProgramParseTest, ProgramWithFunctionDecl) {
  auto* unit = Parse(
      "program p;\n"
      "  function int add(int a, int b);\n"
      "    return a + b;\n"
      "  endfunction\n"
      "endprogram\n");
  ASSERT_EQ(unit->programs.size(), 1u);
  EXPECT_EQ(unit->programs[0]->name, "p");
  EXPECT_EQ(unit->programs[0]->decl_kind, ModuleDeclKind::kProgram);
  ASSERT_GE(unit->programs[0]->items.size(), 1u);
  EXPECT_EQ(unit->programs[0]->items[0]->kind, ModuleItemKind::kFunctionDecl);
  EXPECT_EQ(unit->programs[0]->items[0]->name, "add");
}

TEST_F(ProgramParseTest, ProgramWithTaskAndFunction) {
  auto* unit = Parse(
      "program p;\n"
      "  task run;\n"
      "    $display(\"running\");\n"
      "  endtask\n"
      "  function int get_val;\n"
      "    return 42;\n"
      "  endfunction\n"
      "endprogram\n");
  ASSERT_EQ(unit->programs.size(), 1u);
  EXPECT_EQ(unit->programs[0]->name, "p");
  EXPECT_EQ(unit->programs[0]->decl_kind, ModuleDeclKind::kProgram);
  ASSERT_GE(unit->programs[0]->items.size(), 2u);
  EXPECT_EQ(unit->programs[0]->items[0]->kind, ModuleItemKind::kTaskDecl);
  EXPECT_EQ(unit->programs[0]->items[1]->kind, ModuleItemKind::kFunctionDecl);
}

TEST(ProgramDeclaration, MissingEndprogramIsError) {
  auto r = Parse("program p;");
  EXPECT_TRUE(
      ReportedError(r.diags, "expected 'endprogram', got EOF", 1, "24.3"));
}

TEST(ProgramDeclaration, SampleDeclaration) {
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

TEST(ProgramItemsParsing, CannotContainAlways) {
  auto r = Parse(
      "program p;\n"
      "  logic clk, d, q;\n"
      "  always @(posedge clk) q <= d;\n"
      "endprogram\n");
  EXPECT_TRUE(ReportedError(
      r.diags, "always procedures not allowed in programs", 3, "24.3"));
}

TEST(ProgramItemsParsing, CannotContainAlwaysComb) {
  auto r = Parse(
      "program p;\n"
      "  logic a, b;\n"
      "  always_comb b = a;\n"
      "endprogram\n");
  EXPECT_TRUE(ReportedError(
      r.diags, "always procedures not allowed in programs", 3, "24.3"));
}

TEST(ProgramItemsParsing, CannotContainAlwaysFF) {
  auto r = Parse(
      "program p;\n"
      "  logic clk, d, q;\n"
      "  always_ff @(posedge clk) q <= d;\n"
      "endprogram\n");
  EXPECT_TRUE(ReportedError(
      r.diags, "always procedures not allowed in programs", 3, "24.3"));
}

TEST(ProgramItemsParsing, CannotContainAlwaysLatch) {
  auto r = Parse(
      "program p;\n"
      "  logic en, d, q;\n"
      "  always_latch if (en) q <= d;\n"
      "endprogram\n");
  EXPECT_TRUE(ReportedError(
      r.diags, "always procedures not allowed in programs", 3, "24.3"));
}

TEST(ProgramItemsParsing, CannotContainModuleInst) {
  auto r = Parse(
      "module sub; endmodule\n"
      "program p;\n"
      "  sub u0();\n"
      "endprogram\n");
  EXPECT_TRUE(ReportedError(r.diags, "instantiations not allowed in programs",
                            3, "24.3"));
}

TEST(ProgramItemsParsing, CannotContainGateInst) {
  auto r = Parse(
      "program p;\n"
      "  wire a, b, y;\n"
      "  nand g1(y, a, b);\n"
      "endprogram\n");
  EXPECT_TRUE(ReportedError(
      r.diags, "primitive instances not allowed in programs", 3, "24.3"));
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
  EXPECT_TRUE(ReportedError(
      r.diags, "primitive instances not allowed in programs", 6, "24.3"));
}

TEST(ProgramItemsParsing, CannotContainInterfaceInst) {
  auto r = Parse(
      "interface ifc; endinterface\n"
      "program p;\n"
      "  ifc i0();\n"
      "endprogram\n");
  EXPECT_TRUE(ReportedError(r.diags, "instantiations not allowed in programs",
                            3, "24.3"));
}

TEST(ProgramItemsParsing, CannotContainProgramInst) {
  auto r = Parse(
      "program other; endprogram\n"
      "program p;\n"
      "  other o0();\n"
      "endprogram\n");
  EXPECT_TRUE(ReportedError(r.diags, "instantiations not allowed in programs",
                            3, "24.3"));
}

TEST(ProgramDeclaration, AnonymousProgramAcceptsTaskFunctionClass) {
  auto r = Parse(
      "program;\n"
      "  task anon_t; endtask\n"
      "  function int anon_f; return 0; endfunction\n"
      "  class anon_c; int data; endclass\n"
      "endprogram\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  EXPECT_TRUE(r.cu->programs.empty());
  bool saw_task = false, saw_func = false, saw_class = false;
  for (const auto* item : r.cu->cu_items) {
    EXPECT_TRUE(item->from_anonymous_program);
    if (item->kind == ModuleItemKind::kTaskDecl && item->name == "anon_t")
      saw_task = true;
    if (item->kind == ModuleItemKind::kFunctionDecl && item->name == "anon_f")
      saw_func = true;
    if (item->kind == ModuleItemKind::kClassDecl && item->name == "anon_c")
      saw_class = true;
  }
  EXPECT_TRUE(saw_task);
  EXPECT_TRUE(saw_func);
  EXPECT_TRUE(saw_class);
}

TEST(ProgramDeclaration, AnonymousProgramAllowsEmptyItemAndCovergroup) {
  auto r = Parse(
      "program;\n"
      "  ;\n"
      "  covergroup cg_anon @(posedge clk);\n"
      "    coverpoint clk;\n"
      "  endgroup\n"
      "endprogram\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
}

// The rejecting half of the pair below: a program_ansi_header whose package
// import is followed by neither a parameter_port_list nor a
// list_of_port_declarations is not a program_declaration. The same
// requirement stated once for each of the three ansi headers that may carry
// a header import lives in test_parser_subclause_26_04.cpp.
TEST(ProgramDeclaration, AnsiHeaderPackageImportWithoutPortListFails) {
  auto r = Parse(
      "package pkg;\n"
      "  int x;\n"
      "endpackage\n"
      "program prg import pkg::*;\n"
      "endprogram\n");
  // The three ansi headers share one report, filed under §23.2.1 by
  // Parser::ParseParamsPortsAndSemicolon in src/parser/parser_port.cpp rather
  // than under this file's §24.3.
  EXPECT_TRUE(ReportedError(r.diags,
                            "package_import_declaration in ansi header must be "
                            "followed by parameter_port_list or "
                            "list_of_port_declarations",
                            4, "23.2.1"));
}

TEST(ProgramDeclaration, AnsiHeaderPackageImportWithPortListSucceeds) {
  auto r = Parse(
      "package pkg;\n"
      "  int x;\n"
      "endpackage\n"
      "program prg import pkg::*; (input logic clk);\n"
      "endprogram\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  ASSERT_EQ(r.cu->programs.size(), 1u);
  EXPECT_EQ(r.cu->programs[0]->name, "prg");
  ASSERT_EQ(r.cu->programs[0]->ports.size(), 1u);
  EXPECT_EQ(r.cu->programs[0]->ports[0].name, "clk");
}

TEST(ProgramDeclaration, AnonymousProgramAllowsInterfaceClassDecl) {
  auto r = Parse(
      "program;\n"
      "  interface class iface_c;\n"
      "    pure virtual function int get();\n"
      "  endclass\n"
      "endprogram\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
}

// ---------------------------------------------------------------------------
// The admitting half of A.1.11's closed set, which Syntax 24-1 reproduces in
// this clause labelled as an excerpt from Annex A. Each case below writes one
// alternative the production does admit and reads the item back, so the check
// over an anonymous program's body is shown to be a filter over the kinds
// A.1.11 lists rather than a blanket rejection of what an anonymous program
// holds. The cases for the kinds it excludes live in
// test/src/unit/test_parser_annex_a_01_11.cpp.
//
// §24.6 admits an anonymous program at compilation-unit scope, which is where
// these stand: it declares no scope of its own, so its items land in the
// compilation unit's own item list and that is where each case finds them.
// ---------------------------------------------------------------------------

// The report an item outside A.1.11's set draws, named here so a case can
// claim it did not fire over an item inside the set.
constexpr std::string_view kExcludedItemMessage =
    "an anonymous program may contain only task, function, class, interface "
    "class, covergroup, and class constructor declarations";

// A compilation unit whose only description is an anonymous program holding
// `item` and nothing else.
ParseResult ParseAnonymousProgramHolding(const std::string& item) {
  return Parse("program;\n" + item + "\nendprogram\n");
}

// Whether the anonymous program's one item reached the compilation unit as an
// item of kind `kind`, unreported and marked as having come from an anonymous
// program. FilterAnonymousProgramItems in src/parser/parser.cpp marks only the
// items it keeps, and ValidateNameSpaceCompilationUnit in
// src/elaborator/elaborator_validate_config.cpp reads that mark, so an item
// kept without it is checked as though no anonymous program had held it.
void ExpectAnonymousProgramKept(const ParseResult& r, ModuleItemKind kind) {
  EXPECT_EQ(FindDiag(r, kExcludedItemMessage), nullptr);
  ASSERT_NE(r.cu, nullptr);
  EXPECT_TRUE(r.cu->programs.empty());
  ASSERT_EQ(r.cu->cu_items.size(), 1u);
  EXPECT_EQ(r.cu->cu_items[0]->kind, kind);
  EXPECT_TRUE(r.cu->cu_items[0]->from_anonymous_program);
}

TEST(ProgramDeclaration, AnonymousProgramKeepsTaskDeclaration) {
  auto r = ParseAnonymousProgramHolding("  task anon_task; endtask");
  ExpectAnonymousProgramKept(r, ModuleItemKind::kTaskDecl);
}

TEST(ProgramDeclaration, AnonymousProgramKeepsFunctionDeclaration) {
  auto r = ParseAnonymousProgramHolding(
      "  function int anon_func; return 0; endfunction");
  ExpectAnonymousProgramKept(r, ModuleItemKind::kFunctionDecl);
}

TEST(ProgramDeclaration, AnonymousProgramKeepsClassDeclaration) {
  auto r = ParseAnonymousProgramHolding("  class anon_class; endclass");
  ExpectAnonymousProgramKept(r, ModuleItemKind::kClassDecl);
  ASSERT_EQ(r.cu->cu_items.size(), 1u);
  ASSERT_NE(r.cu->cu_items[0]->class_decl, nullptr);
  EXPECT_FALSE(r.cu->cu_items[0]->class_decl->is_interface);
}

// interface_class_declaration is its own alternative of anonymous_program_item
// and the parser records it under the same kind as a class_declaration, so the
// case reads the flag that tells the two apart rather than the kind alone.
TEST(ProgramDeclaration, AnonymousProgramKeepsInterfaceClassDeclaration) {
  auto r = ParseAnonymousProgramHolding(
      "  interface class anon_iface_class;\n"
      "    pure virtual function int get();\n"
      "  endclass");
  ExpectAnonymousProgramKept(r, ModuleItemKind::kClassDecl);
  ASSERT_EQ(r.cu->cu_items.size(), 1u);
  ASSERT_NE(r.cu->cu_items[0]->class_decl, nullptr);
  EXPECT_TRUE(r.cu->cu_items[0]->class_decl->is_interface);
}

TEST(ProgramDeclaration, AnonymousProgramKeepsCovergroupDeclaration) {
  auto r = ParseAnonymousProgramHolding("  covergroup anon_cg; endgroup");
  ExpectAnonymousProgramKept(r, ModuleItemKind::kCovergroupDecl);
}

// class_constructor_declaration is its own alternative of
// anonymous_program_item and the parser records an out-of-block `new` as a
// function declaration carrying the class it belongs to, so the case reads
// that name as well as the kind.
TEST(ProgramDeclaration, AnonymousProgramKeepsClassConstructorDeclaration) {
  auto r = ParseAnonymousProgramHolding(
      "  function anon_ctor_class::new(); endfunction");
  ExpectAnonymousProgramKept(r, ModuleItemKind::kFunctionDecl);
  ASSERT_EQ(r.cu->cu_items.size(), 1u);
  EXPECT_EQ(r.cu->cu_items[0]->method_class, "anon_ctor_class");
  EXPECT_EQ(r.cu->cu_items[0]->name, "new");
}

// A.1.11's last alternative is a bare `;`, and what it declares is nothing:
// the body loop in Parser::TryParseAnonymousProgram consumes the semicolon
// before ParseModuleItem is reached, so no item is built and none reaches the
// filter. The compilation unit is therefore empty rather than holding an item
// of some kind that a filter over kinds would then have to admit.
TEST(ProgramDeclaration, AnonymousProgramNullItemDeclaresNothing) {
  auto r = ParseAnonymousProgramHolding("  ;");
  EXPECT_EQ(FindDiag(r, kExcludedItemMessage), nullptr);
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  EXPECT_TRUE(r.cu->cu_items.empty());
}

}  // namespace
