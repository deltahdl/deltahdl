// §24.3: The program construct

#include <gtest/gtest.h>

#include <string>

#include "common/arena.h"
#include "common/diagnostic.h"
#include "common/source_mgr.h"
#include "elaboration/elaborator.h"
#include "elaboration/rtlir.h"
#include "lexer/lexer.h"
#include "parser/ast.h"
#include "parser/parser.h"
#include "simulation/process.h"
#include "simulation/scheduler.h"
#include "simulation/sim_context.h"

using namespace delta;

// =============================================================================
// Parse-level fixture
// =============================================================================
struct ProgramTestParse : ::testing::Test {
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
// Elaboration fixture
// =============================================================================
struct ProgramElabFixture {
  SourceManager mgr;
  Arena arena;
  DiagEngine diag{mgr};
};

static const ModuleItem *FindItemOfKind(const std::vector<ModuleItem *> &items,
                                        ModuleItemKind kind) {
  for (const auto *item : items) {
    if (item->kind == kind) return item;
  }
  return nullptr;
}

static int CountItemsOfKind(const std::vector<ModuleItem *> &items,
                            ModuleItemKind kind) {
  int count = 0;
  for (const auto *item : items) {
    if (item->kind == kind) ++count;
  }
  return count;
}

namespace {

TEST_F(ProgramTestParse, ProgramWithEndLabel) {
  auto *unit = Parse("program my_prog; endprogram : my_prog");
  ASSERT_EQ(unit->programs.size(), 1u);
  EXPECT_EQ(unit->programs[0]->name, "my_prog");
}

TEST_F(ProgramTestParse, ProgramAutomaticLifetime) {
  auto *unit = Parse("program automatic auto_prog; endprogram");
  ASSERT_EQ(unit->programs.size(), 1u);
  EXPECT_EQ(unit->programs[0]->name, "auto_prog");
  EXPECT_EQ(unit->programs[0]->decl_kind, ModuleDeclKind::kProgram);
}

// =============================================================================
// §24.2 Program ports
// =============================================================================
TEST_F(ProgramTestParse, ProgramWithPorts) {
  auto *unit = Parse(
      "program p(input logic clk, input logic rst, output logic done);\n"
      "endprogram\n");
  ASSERT_EQ(unit->programs.size(), 1u);
  ASSERT_GE(unit->programs[0]->ports.size(), 3u);
  EXPECT_EQ(unit->programs[0]->ports[0].name, "clk");
  EXPECT_EQ(unit->programs[0]->ports[0].direction, Direction::kInput);
  EXPECT_EQ(unit->programs[0]->ports[2].name, "done");
  EXPECT_EQ(unit->programs[0]->ports[2].direction, Direction::kOutput);
}

TEST_F(ProgramTestParse, ProgramWithParameters) {
  auto *unit = Parse(
      "program p #(parameter WIDTH = 8)(input logic [WIDTH-1:0] data);\n"
      "endprogram\n");
  ASSERT_EQ(unit->programs.size(), 1u);
  ASSERT_EQ(unit->programs[0]->params.size(), 1u);
  EXPECT_EQ(unit->programs[0]->params[0].first, "WIDTH");
}

// =============================================================================
// §24.3 Program with initial blocks (reactive region scheduling)
// =============================================================================
TEST_F(ProgramTestParse, ProgramWithInitialBlock) {
  auto *unit = Parse(
      "program p;\n"
      "  initial begin\n"
      "    $display(\"test\");\n"
      "  end\n"
      "endprogram\n");
  ASSERT_EQ(unit->programs.size(), 1u);
  ASSERT_EQ(unit->programs[0]->items.size(), 1u);
  EXPECT_EQ(unit->programs[0]->items[0]->kind, ModuleItemKind::kInitialBlock);
}

TEST_F(ProgramTestParse, ProgramWithMultipleInitialBlocks) {
  auto *unit = Parse(
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
// §24.4 Program with task/function declarations
// =============================================================================
TEST_F(ProgramTestParse, ProgramWithTask) {
  auto *unit = Parse(
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
  auto *unit = Parse(
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
// §24.6 Program instantiation
// =============================================================================
TEST_F(ProgramTestParse, ProgramInstantiatedInModule) {
  auto *unit = Parse(
      "program test_prog(input logic clk);\n"
      "endprogram\n"
      "module top;\n"
      "  logic clk;\n"
      "  test_prog tp(.clk(clk));\n"
      "endmodule\n");
  ASSERT_EQ(unit->programs.size(), 1u);
  ASSERT_EQ(unit->modules.size(), 1u);
  const auto *inst =
      FindItemOfKind(unit->modules[0]->items, ModuleItemKind::kModuleInst);
  ASSERT_NE(inst, nullptr);
  EXPECT_EQ(inst->inst_module, "test_prog");
  EXPECT_EQ(inst->inst_name, "tp");
}

// =============================================================================
// §24.7 Multiple programs and coexistence
// =============================================================================
TEST_F(ProgramTestParse, MultipleProgramsCoexist) {
  auto *unit = Parse(
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
  auto *unit = Parse(
      "program p;\n"
      "  logic [31:0] data;\n"
      "  logic [7:0] addr;\n"
      "endprogram\n");
  ASSERT_EQ(unit->programs.size(), 1u);
  EXPECT_GE(unit->programs[0]->items.size(), 2u);
}

}  // namespace
