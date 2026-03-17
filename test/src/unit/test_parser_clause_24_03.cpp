#include "fixture_parser.h"
#include "fixture_program.h"
#include "helpers_parser_verify.h"

using namespace delta;

namespace {

TEST(SourceText, ProgramParamsAndPorts) {
  auto r = Parse(
      "program prg #(parameter int N = 10)(input logic clk);\n"
      "endprogram\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  ASSERT_EQ(r.cu->programs.size(), 1u);
  EXPECT_EQ(r.cu->programs[0]->params.size(), 1u);
  EXPECT_EQ(r.cu->programs[0]->ports.size(), 1u);
}

TEST(SchedulingSemanticsParsing, ProgramBlockDeterministicScheduling) {
  auto r = Parse(
      "program p;\n"
      "endprogram\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  ASSERT_EQ(r.cu->programs.size(), 1u);
  EXPECT_EQ(r.cu->programs[0]->name, "p");
  EXPECT_EQ(r.cu->programs[0]->decl_kind, ModuleDeclKind::kProgram);
}

TEST(Parser, ProgramWithInitial) {
  auto r = Parse(
      "program test_prog;\n"
      "  initial $display(\"hello\");\n"
      "endprogram\n");
  ASSERT_NE(r.cu, nullptr);
  ASSERT_EQ(r.cu->programs.size(), 1);
  EXPECT_EQ(r.cu->programs[0]->items.size(), 1);
  EXPECT_EQ(r.cu->programs[0]->items[0]->kind, ModuleItemKind::kInitialBlock);
}

TEST(SchedulingSemanticsParsing, ProgramWithInitialBlock) {
  auto r = Parse(
      "program p;\n"
      "  initial begin\n"
      "    $display(\"test\");\n"
      "  end\n"
      "endprogram\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  ASSERT_EQ(r.cu->programs.size(), 1u);
  ASSERT_EQ(r.cu->programs[0]->items.size(), 1u);
  EXPECT_EQ(r.cu->programs[0]->items[0]->kind, ModuleItemKind::kInitialBlock);
}

TEST_F(ProgramTestParse, ProgramAutomaticLifetime) {
  auto* unit = Parse("program automatic auto_prog; endprogram");
  ASSERT_EQ(unit->programs.size(), 1u);
  EXPECT_EQ(unit->programs[0]->name, "auto_prog");
  EXPECT_EQ(unit->programs[0]->decl_kind, ModuleDeclKind::kProgram);
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

TEST(SchedulingSemanticsParsing, ProgramWithFunction) {
  EXPECT_TRUE(
      ParseOk("program p;\n"
              "  function automatic int get_val();\n"
              "    automatic int v = 10;\n"
              "    return v;\n"
              "  endfunction\n"
              "  initial begin\n"
              "    $display(get_val());\n"
              "  end\n"
              "endprogram\n"));
}

TEST_F(ProgramTestParse, ProgramWithTask) {
  auto* unit = Parse(
      "program p;\n"
      "  task run_test;\n"
      "    $display(\"running\");\n"
      "  endtask\n"
      "endprogram\n");
  ASSERT_EQ(unit->programs.size(), 1u);
  ASSERT_GE(unit->programs[0]->items.size(), 1u);
  EXPECT_EQ(unit->programs[0]->items[0]->kind, ModuleItemKind::kTaskDecl);
  EXPECT_EQ(unit->programs[0]->items[0]->name, "run_test");
}

TEST_F(ProgramTestParse, ProgramWithFunction) {
  auto* unit = Parse(
      "program p;\n"
      "  function int compute(int a, int b);\n"
      "    return a + b;\n"
      "  endfunction\n"
      "endprogram\n");
  ASSERT_EQ(unit->programs.size(), 1u);
  ASSERT_GE(unit->programs[0]->items.size(), 1u);
  EXPECT_EQ(unit->programs[0]->items[0]->kind, ModuleItemKind::kFunctionDecl);
  EXPECT_EQ(unit->programs[0]->items[0]->name, "compute");
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

TEST_F(ProgramTestParse, ProgramWithVariableDecls) {
  auto* unit = Parse(
      "program p;\n"
      "  logic [31:0] data;\n"
      "  logic [7:0] addr;\n"
      "endprogram\n");
  ASSERT_EQ(unit->programs.size(), 1u);
  EXPECT_GE(unit->programs[0]->items.size(), 2u);
}

TEST(SchedulingSemanticsParsing, TaskInProgramBlock) {
  EXPECT_TRUE(
      ParseOk("program test_prog;\n"
              "  task run_test();\n"
              "    int x;\n"
              "    x = 1;\n"
              "    $display(\"x=%0d\", x);\n"
              "  endtask\n"
              "endprogram\n"));
}

TEST(SchedulingSemanticsParsing, ProgramBlock) {
  auto r = Parse(
      "program test_prog;\n"
      "  initial begin\n"
      "    $display(\"reactive region\");\n"
      "  end\n"
      "endprogram\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  ASSERT_EQ(r.cu->programs.size(), 1u);
  EXPECT_EQ(r.cu->programs[0]->name, "test_prog");
  EXPECT_EQ(r.cu->programs[0]->decl_kind, ModuleDeclKind::kProgram);
  ASSERT_FALSE(r.cu->programs[0]->items.empty());
  EXPECT_EQ(r.cu->programs[0]->items[0]->kind, ModuleItemKind::kInitialBlock);
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

TEST_F(ProgramParseTest, ProgramCoexistsWithModule) {
  auto* unit = Parse(
      "module m;\n"
      "endmodule\n"
      "program p;\n"
      "endprogram\n");
  ASSERT_EQ(unit->modules.size(), 1u);
  EXPECT_EQ(unit->modules[0]->name, "m");
  ASSERT_EQ(unit->programs.size(), 1u);
  EXPECT_EQ(unit->programs[0]->name, "p");
  EXPECT_EQ(unit->programs[0]->decl_kind, ModuleDeclKind::kProgram);
}

TEST_F(ProgramParseTest, MultipleProgramsInCompilationUnit) {
  auto* unit = Parse(
      "program p1;\n"
      "endprogram\n"
      "program p2;\n"
      "endprogram\n");
  ASSERT_EQ(unit->programs.size(), 2u);
  EXPECT_EQ(unit->programs[0]->name, "p1");
  EXPECT_EQ(unit->programs[0]->decl_kind, ModuleDeclKind::kProgram);
  EXPECT_EQ(unit->programs[1]->name, "p2");
  EXPECT_EQ(unit->programs[1]->decl_kind, ModuleDeclKind::kProgram);
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

TEST(DesignBuildingBlockParsing, ProgramBlockWithDeclarations) {
  auto r = Parse(
      "program test_prog;\n"
      "  int count;\n"
      "  initial begin\n"
      "    count = 0;\n"
      "  end\n"
      "endprogram\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  ASSERT_EQ(r.cu->programs.size(), 1u);
  EXPECT_EQ(r.cu->programs[0]->name, "test_prog");
  EXPECT_EQ(r.cu->programs[0]->decl_kind, ModuleDeclKind::kProgram);
  EXPECT_FALSE(r.cu->programs[0]->items.empty());
}

TEST(ProgramEndLabel, EndLabelMatchesProgramName) {
  auto r = Parse("program qux; endprogram : qux\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  ASSERT_EQ(r.cu->programs.size(), 1u);
  EXPECT_EQ(r.cu->programs[0]->name, "qux");
}

TEST(ProgramDeclaration, MissingEndprogramIsError) {
  EXPECT_FALSE(ParseOk("program p;"));
}

TEST(ProgramDeclarations, ProgramKeywordIntroducesProgram) {
  auto r = Parse("program p; endprogram");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  ASSERT_EQ(r.cu->programs.size(), 1u);
  EXPECT_EQ(r.cu->programs[0]->decl_kind, ModuleDeclKind::kProgram);
}

TEST(ProgramDeclarations, ProgramContainsDeclarationsAndCode) {
  auto r = Parse(
      "program p;\n"
      "  logic a;\n"
      "  initial a = 1;\n"
      "endprogram\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  EXPECT_FALSE(r.cu->programs[0]->items.empty());
}

TEST(ProgramDeclaration, EnclosedByKeywords) {
  auto r = Parse("program p; endprogram");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  ASSERT_EQ(r.cu->programs.size(), 1u);
  EXPECT_EQ(r.cu->programs[0]->name, "p");
  EXPECT_EQ(r.cu->programs[0]->decl_kind, ModuleDeclKind::kProgram);
}

TEST(ProgramDeclaration, WithPorts) {
  auto r = Parse(
      "program p(input clk, input [16:1] addr, inout [7:0] data);\n"
      "endprogram\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  EXPECT_EQ(r.cu->programs[0]->ports.size(), 3u);
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

}  // namespace
