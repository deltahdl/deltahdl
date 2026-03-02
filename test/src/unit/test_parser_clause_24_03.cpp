// §24.3: The program construct

#include "fixture_parser.h"
#include "helpers_parser_verify.h"

using namespace delta;

namespace {

// =============================================================================
// A.4.1.3 -- Program instantiation
//
// program_instantiation ::=
//   program_identifier [ parameter_value_assignment ]
//     hierarchical_instance { , hierarchical_instance } ;
// =============================================================================
// --- program_instantiation: basic ---
TEST(ParserAnnexA0413, BasicProgramInst) {
  auto r = Parse(
      "program my_prog(input logic clk);\n"
      "endprogram\n"
      "module m; my_prog u0(.clk(clk)); endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* item = r.cu->modules[0]->items[0];
  EXPECT_EQ(item->kind, ModuleItemKind::kModuleInst);
  EXPECT_EQ(item->inst_module, "my_prog");
  EXPECT_EQ(item->inst_name, "u0");
}

// --- program_instantiation: multiple hierarchical_instance ---
TEST(ParserAnnexA0413, MultipleProgramInstances) {
  auto r = Parse(
      "program my_prog(input logic clk);\n"
      "endprogram\n"
      "module m; my_prog u0(.clk(a)), u1(.clk(b)); endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  ASSERT_GE(r.cu->modules[0]->items.size(), 2u);
  auto* i0 = r.cu->modules[0]->items[0];
  auto* i1 = r.cu->modules[0]->items[1];
  EXPECT_EQ(i0->inst_module, "my_prog");
  EXPECT_EQ(i0->inst_name, "u0");
  EXPECT_EQ(i1->inst_module, "my_prog");
  EXPECT_EQ(i1->inst_name, "u1");
}

// Program parameter port list and ports
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

struct ParseResult4d {
  SourceManager mgr;
  Arena arena;
  CompilationUnit* cu = nullptr;
  bool has_errors = false;
};

static ParseResult4d Parse(const std::string& src) {
  ParseResult4d result;
  auto fid = result.mgr.AddFile("<test>", src);
  DiagEngine diag(result.mgr);
  Lexer lexer(result.mgr.FileContent(fid), fid, diag);
  Parser parser(lexer, result.arena, diag);
  result.cu = parser.Parse();
  result.has_errors = diag.HasErrors();
  return result;
}

// =============================================================================
// §4.6: Program block for deterministic test scheduling
// =============================================================================
TEST(ParserSection4, Sec4_6_ProgramBlockDeterministicScheduling) {
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

// =============================================================================
// §4.6: Program block with initial block
// =============================================================================
TEST(ParserSection4, Sec4_6_ProgramWithInitialBlock) {
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

// =============================================================================
// 30. Program block with function parses
// =============================================================================
TEST(ParserSection4, Sec4_9_4_ProgramWithFunction) {
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

// =============================================================================
// §24.4 Program with task/function declarations
// =============================================================================
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

// =============================================================================
// §24.7 Multiple programs and coexistence
// =============================================================================
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

// =============================================================================
// §24.8 Program with variable declarations
// =============================================================================
TEST_F(ProgramTestParse, ProgramWithVariableDecls) {
  auto* unit = Parse(
      "program p;\n"
      "  logic [31:0] data;\n"
      "  logic [7:0] addr;\n"
      "endprogram\n");
  ASSERT_EQ(unit->programs.size(), 1u);
  EXPECT_GE(unit->programs[0]->items.size(), 2u);
}

// anonymous_program_item: class_declaration, interface_class_declaration
TEST(SourceText, AnonymousProgramClasses) {
  auto r = Parse(
      "package pkg;\n"
      "  program;\n"
      "    class C; endclass\n"
      "    interface class IC;\n"
      "      pure virtual function void f();\n"
      "    endclass\n"
      "  endprogram\n"
      "endpackage\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  ASSERT_EQ(r.cu->packages.size(), 1u);
}

// =============================================================================
// 30. Task in program block (automatic by default)
// =============================================================================
TEST(ParserSection4, Sec4_9_3_TaskInProgramBlock) {
  EXPECT_TRUE(
      ParseOk("program test_prog;\n"
              "  task run_test();\n"
              "    int x;\n"
              "    x = 1;\n"
              "    $display(\"x=%0d\", x);\n"
              "  endtask\n"
              "endprogram\n"));
}

// anonymous_program_item: covergroup, class_constructor, ;
TEST(SourceText, AnonymousProgramMisc) {
  auto r = Parse(
      "package pkg;\n"
      "  program;\n"
      "    covergroup cg; endgroup\n"
      "    function MyClass::new(); endfunction\n"
      "    ;\n"
      "  endprogram\n"
      "endpackage\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  ASSERT_EQ(r.cu->packages.size(), 1u);
}

struct ParseResult4c {
  SourceManager mgr;
  Arena arena;
  CompilationUnit* cu = nullptr;
  bool has_errors = false;
};

static ParseResult4c Parse(const std::string& src) {
  ParseResult4c result;
  auto fid = result.mgr.AddFile("<test>", src);
  DiagEngine diag(result.mgr);
  Lexer lexer(result.mgr.FileContent(fid), fid, diag);
  Parser parser(lexer, result.arena, diag);
  result.cu = parser.Parse();
  result.has_errors = diag.HasErrors();
  return result;
}

// ---------------------------------------------------------------------------
// 24. Program block (Reactive region)
// ---------------------------------------------------------------------------
TEST(ParserSection4, Sec4_5_ProgramBlock) {
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

using ProgramParseTest = ProgramTestParse;

// =============================================================================
// §24.1 Basic program declarations
// =============================================================================
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

// =============================================================================
// §24.2 Program ports and parameters
// =============================================================================
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

// =============================================================================
// §24.3 Program body items
// =============================================================================
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

// =============================================================================
// §24.4 Multiple programs and coexistence with modules
// =============================================================================
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

// =============================================================================
// §24.6 Program with task and function declarations
// =============================================================================
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

// =============================================================================
// A.1.7 Program items
// =============================================================================
// program_item ::= port_declaration ;
TEST(SourceText, ProgramItemPortDecl) {
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

// Returns true if any item in the list matches the given kind.
bool HasItemKind(const std::vector<ModuleItem*>& items, ModuleItemKind kind) {
  for (auto* item : items) {
    if (item->kind == kind) return true;
  }
  return false;
}

// non_port_program_item ::= continuous_assign
TEST(SourceText, ProgramContinuousAssign) {
  auto r = Parse(
      "program prg;\n"
      "  logic a, b;\n"
      "  assign a = b;\n"
      "endprogram\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  ASSERT_EQ(r.cu->programs.size(), 1u);
  EXPECT_TRUE(
      HasItemKind(r.cu->programs[0]->items, ModuleItemKind::kContAssign));
}

// Returns true if any item matches the given kind and name.
bool HasItemKindNamed(const std::vector<ModuleItem*>& items,
                      ModuleItemKind kind, std::string_view name) {
  for (auto* item : items) {
    if (item->kind == kind && item->name == name) return true;
  }
  return false;
}

// non_port_program_item ::= module_or_generate_item_declaration
TEST(SourceText, ProgramModuleOrGenerateItemDecl) {
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

// non_port_program_item ::= initial_construct
TEST(SourceText, ProgramInitialConstruct) {
  auto r = Parse(
      "program prg;\n"
      "  initial begin\n"
      "    $display(\"hello\");\n"
      "  end\n"
      "endprogram\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  ASSERT_EQ(r.cu->programs.size(), 1u);
  EXPECT_TRUE(
      HasItemKind(r.cu->programs[0]->items, ModuleItemKind::kInitialBlock));
}

// non_port_program_item ::= final_construct
TEST(SourceText, ProgramFinalConstruct) {
  auto r = Parse(
      "program prg;\n"
      "  final begin\n"
      "    $display(\"done\");\n"
      "  end\n"
      "endprogram\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  ASSERT_EQ(r.cu->programs.size(), 1u);
  EXPECT_TRUE(
      HasItemKind(r.cu->programs[0]->items, ModuleItemKind::kFinalBlock));
}

// non_port_program_item ::= concurrent_assertion_item
TEST(SourceText, ProgramConcurrentAssertion) {
  auto r = Parse(
      "program prg;\n"
      "  logic clk, a;\n"
      "  assert property (@(posedge clk) a);\n"
      "endprogram\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  ASSERT_EQ(r.cu->programs.size(), 1u);
  EXPECT_TRUE(
      HasItemKind(r.cu->programs[0]->items, ModuleItemKind::kAssertProperty));
}

// program_generate_item ::= conditional_generate_construct
TEST(SourceText, ProgramGenerateConditional) {
  auto r = Parse(
      "program prg;\n"
      "  parameter P = 1;\n"
      "  if (P) begin : blk\n"
      "    int x;\n"
      "  end\n"
      "endprogram\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  ASSERT_EQ(r.cu->programs.size(), 1u);
  EXPECT_TRUE(
      HasItemKind(r.cu->programs[0]->items, ModuleItemKind::kGenerateIf));
}

// program_generate_item ::= generate_region
TEST(SourceText, ProgramGenerateRegion) {
  auto r = Parse(
      "program prg;\n"
      "  generate\n"
      "    int x;\n"
      "  endgenerate\n"
      "endprogram\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  ASSERT_EQ(r.cu->programs.size(), 1u);
  EXPECT_FALSE(r.cu->programs[0]->items.empty());
}

// Combined: program with multiple A.1.7 item types.
TEST(SourceText, ProgramMultipleItemTypes) {
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
  EXPECT_TRUE(HasItemKind(items, ModuleItemKind::kVarDecl));
  EXPECT_TRUE(HasItemKind(items, ModuleItemKind::kContAssign));
  EXPECT_TRUE(HasItemKind(items, ModuleItemKind::kInitialBlock));
  EXPECT_TRUE(HasItemKind(items, ModuleItemKind::kFinalBlock));
  EXPECT_TRUE(HasItemKind(items, ModuleItemKind::kAssertProperty));
  EXPECT_TRUE(HasItemKind(items, ModuleItemKind::kElabSystemTask));
}

// 17. Program block with declarations
TEST(ParserClause03, Cl3_13_ProgramBlockWithDeclarations) {
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

// description: program_declaration
TEST(SourceText, DescriptionProgram) {
  auto r = Parse("program prg; endprogram\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  ASSERT_EQ(r.cu->programs.size(), 1u);
  EXPECT_EQ(r.cu->programs[0]->name, "prg");
}

// =============================================================================
// A.1.2 program_declaration — all forms
// =============================================================================
// Program with lifetime.
TEST(SourceText, ProgramWithLifetime) {
  auto r = Parse("program automatic prg; endprogram\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  ASSERT_EQ(r.cu->programs.size(), 1u);
}

}  // namespace
