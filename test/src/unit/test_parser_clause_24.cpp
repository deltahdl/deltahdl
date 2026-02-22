// Tests for §24 Programs

#include <gtest/gtest.h>

#include "common/arena.h"
#include "common/diagnostic.h"
#include "common/source_mgr.h"
#include "lexer/lexer.h"
#include "parser/ast.h"
#include "parser/parser.h"

using namespace delta;

namespace {

struct ProgramParseTest : ::testing::Test {
protected:
  CompilationUnit *Parse(const std::string &src) {
    source_ = src;
    lexer_ = std::make_unique<Lexer>(source_, 0, diag_);
    parser_ = std::make_unique<Parser>(*lexer_, arena_, diag_);
    return parser_->Parse();
  }

  SourceManager mgr_;
  Arena arena_;
  DiagEngine diag_{mgr_};
  std::string source_;
  std::unique_ptr<Lexer> lexer_;
  std::unique_ptr<Parser> parser_;
};

// =============================================================================
// §24.1 Basic program declarations
// =============================================================================

TEST_F(ProgramParseTest, EmptyProgram) {
  auto *unit = Parse("program p; endprogram");
  ASSERT_EQ(unit->programs.size(), 1u);
  EXPECT_EQ(unit->programs[0]->name, "p");
  EXPECT_EQ(unit->programs[0]->decl_kind, ModuleDeclKind::kProgram);
  EXPECT_TRUE(unit->programs[0]->ports.empty());
  EXPECT_TRUE(unit->programs[0]->params.empty());
  EXPECT_TRUE(unit->programs[0]->items.empty());
}

TEST_F(ProgramParseTest, ProgramWithEndLabel) {
  auto *unit = Parse("program p; endprogram : p");
  ASSERT_EQ(unit->programs.size(), 1u);
  EXPECT_EQ(unit->programs[0]->name, "p");
  EXPECT_EQ(unit->programs[0]->decl_kind, ModuleDeclKind::kProgram);
}

// =============================================================================
// §24.2 Program ports and parameters
// =============================================================================

TEST_F(ProgramParseTest, ProgramWithPorts) {
  auto *unit = Parse("program p(input logic clk, input logic rst);\n"
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
  auto *unit = Parse("program p #(parameter N = 8)(input logic clk);\n"
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
  auto *unit = Parse("program p;\n"
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

TEST_F(ProgramParseTest, ProgramWithFinalBlock) {
  auto *unit = Parse("program p;\n"
                     "  final begin\n"
                     "    $display(\"done\");\n"
                     "  end\n"
                     "endprogram\n");
  ASSERT_EQ(unit->programs.size(), 1u);
  EXPECT_EQ(unit->programs[0]->name, "p");
  EXPECT_EQ(unit->programs[0]->decl_kind, ModuleDeclKind::kProgram);
  ASSERT_EQ(unit->programs[0]->items.size(), 1u);
  EXPECT_EQ(unit->programs[0]->items[0]->kind, ModuleItemKind::kFinalBlock);
}

TEST_F(ProgramParseTest, ProgramWithMultipleItems) {
  auto *unit = Parse("program p;\n"
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

TEST_F(ProgramParseTest, ProgramWithImportStatement) {
  auto *unit = Parse("program p;\n"
                     "  import pkg::*;\n"
                     "endprogram\n");
  ASSERT_EQ(unit->programs.size(), 1u);
  EXPECT_EQ(unit->programs[0]->name, "p");
  EXPECT_EQ(unit->programs[0]->decl_kind, ModuleDeclKind::kProgram);
  ASSERT_EQ(unit->programs[0]->items.size(), 1u);
  EXPECT_EQ(unit->programs[0]->items[0]->kind, ModuleItemKind::kImportDecl);
  EXPECT_EQ(unit->programs[0]->items[0]->import_item.package_name, "pkg");
  EXPECT_TRUE(unit->programs[0]->items[0]->import_item.is_wildcard);
}

// =============================================================================
// §24.4 Multiple programs and coexistence with modules
// =============================================================================

TEST_F(ProgramParseTest, ProgramCoexistsWithModule) {
  auto *unit = Parse("module m;\n"
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
  auto *unit = Parse("program p1;\n"
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
// §24.5 Program lifetime qualifier
// =============================================================================

TEST_F(ProgramParseTest, ProgramWithAutomaticLifetime) {
  auto *unit = Parse("program automatic p; endprogram");
  ASSERT_EQ(unit->programs.size(), 1u);
  EXPECT_EQ(unit->programs[0]->name, "p");
  EXPECT_EQ(unit->programs[0]->decl_kind, ModuleDeclKind::kProgram);
}

// =============================================================================
// §24.6 Program with task and function declarations
// =============================================================================

TEST_F(ProgramParseTest, ProgramWithTaskDecl) {
  auto *unit = Parse("program p;\n"
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
  auto *unit = Parse("program p;\n"
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
  auto *unit = Parse("program p;\n"
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

} // namespace
