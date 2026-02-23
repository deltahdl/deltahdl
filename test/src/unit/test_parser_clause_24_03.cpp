// §24.3: The program construct

#include <gtest/gtest.h>

#include <string>

#include "common/arena.h"
#include "common/diagnostic.h"
#include "common/source_mgr.h"
#include "lexer/lexer.h"
#include "parser/parser.h"

using namespace delta;

// --- Test helpers ---
struct ParseResult {
  SourceManager mgr;
  Arena arena;
  CompilationUnit *cu = nullptr;
  bool has_errors = false;
};

ParseResult Parse(const std::string &src) {
  ParseResult result;
  auto fid = result.mgr.AddFile("<test>", src);
  DiagEngine diag(result.mgr);
  Lexer lexer(result.mgr.FileContent(fid), fid, diag);
  Parser parser(lexer, result.arena, diag);
  result.cu = parser.Parse();
  result.has_errors = diag.HasErrors();
  return result;
}

// Returns true if any item in the list matches the given kind.
bool HasItemKind(const std::vector<ModuleItem *> &items, ModuleItemKind kind) {
  for (auto *item : items) {
    if (item->kind == kind) return true;
  }
  return false;
}

// Returns true if any item matches the given kind and name.
bool HasItemKindNamed(const std::vector<ModuleItem *> &items,
                      ModuleItemKind kind, std::string_view name) {
  for (auto *item : items) {
    if (item->kind == kind && item->name == name) return true;
  }
  return false;
}

namespace {

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
  auto *p = r.cu->programs[0];
  EXPECT_EQ(p->name, "prg");
  EXPECT_EQ(p->ports.size(), 2u);
  EXPECT_EQ(p->ports[0].direction, Direction::kInput);
  EXPECT_EQ(p->ports[1].direction, Direction::kOutput);
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
  auto &items = r.cu->programs[0]->items;
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

// non_port_program_item ::= timeunits_declaration
TEST(SourceText, ProgramTimeunitsDecl) {
  auto r = Parse(
      "program prg;\n"
      "  timeunit 1ns;\n"
      "  timeprecision 1ps;\n"
      "endprogram\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  ASSERT_EQ(r.cu->programs.size(), 1u);
  EXPECT_EQ(r.cu->programs[0]->name, "prg");
}

// program_generate_item ::= loop_generate_construct
TEST(SourceText, ProgramGenerateLoop) {
  auto r = Parse(
      "program prg;\n"
      "  genvar i;\n"
      "  for (i = 0; i < 4; i = i + 1) begin : blk\n"
      "    int x;\n"
      "  end\n"
      "endprogram\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  ASSERT_EQ(r.cu->programs.size(), 1u);
  EXPECT_TRUE(
      HasItemKind(r.cu->programs[0]->items, ModuleItemKind::kGenerateFor));
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

// program_generate_item ::= elaboration_severity_system_task
TEST(SourceText, ProgramElabSeverityTask) {
  auto r = Parse(
      "program prg;\n"
      "  $info(\"program loaded\");\n"
      "endprogram\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  ASSERT_EQ(r.cu->programs.size(), 1u);
  EXPECT_TRUE(
      HasItemKind(r.cu->programs[0]->items, ModuleItemKind::kElabSystemTask));
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
  auto &items = r.cu->programs[0]->items;
  EXPECT_TRUE(HasItemKind(items, ModuleItemKind::kVarDecl));
  EXPECT_TRUE(HasItemKind(items, ModuleItemKind::kContAssign));
  EXPECT_TRUE(HasItemKind(items, ModuleItemKind::kInitialBlock));
  EXPECT_TRUE(HasItemKind(items, ModuleItemKind::kFinalBlock));
  EXPECT_TRUE(HasItemKind(items, ModuleItemKind::kAssertProperty));
  EXPECT_TRUE(HasItemKind(items, ModuleItemKind::kElabSystemTask));
}

}  // namespace
