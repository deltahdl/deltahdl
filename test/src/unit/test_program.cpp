// Tests for §24 Program declarations — parsing, elaboration, and simulation.

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

namespace {

// =============================================================================
// Parse-level fixture
// =============================================================================

struct ProgramTestParse : ::testing::Test {
 protected:
  CompilationUnit* Parse(const std::string& src) {
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

static RtlirDesign* ElaborateSource(const std::string& src,
                                    ProgramElabFixture& f,
                                    std::string_view top_name) {
  auto fid = f.mgr.AddFile("<test>", src);
  Lexer lexer(f.mgr.FileContent(fid), fid, f.diag);
  Parser parser(lexer, f.arena, f.diag);
  auto* cu = parser.Parse();
  Elaborator elab(f.arena, f.diag, cu);
  return elab.Elaborate(top_name);
}

// =============================================================================
// §24.1 Basic program declaration
// =============================================================================

TEST_F(ProgramTestParse, EmptyProgram) {
  auto* unit = Parse("program p; endprogram");
  ASSERT_EQ(unit->programs.size(), 1u);
  EXPECT_EQ(unit->programs[0]->name, "p");
  EXPECT_EQ(unit->programs[0]->decl_kind, ModuleDeclKind::kProgram);
  EXPECT_TRUE(unit->programs[0]->ports.empty());
  EXPECT_TRUE(unit->programs[0]->items.empty());
}

TEST_F(ProgramTestParse, ProgramWithEndLabel) {
  auto* unit = Parse("program my_prog; endprogram : my_prog");
  ASSERT_EQ(unit->programs.size(), 1u);
  EXPECT_EQ(unit->programs[0]->name, "my_prog");
}

TEST_F(ProgramTestParse, ProgramAutomaticLifetime) {
  auto* unit = Parse("program automatic auto_prog; endprogram");
  ASSERT_EQ(unit->programs.size(), 1u);
  EXPECT_EQ(unit->programs[0]->name, "auto_prog");
  EXPECT_EQ(unit->programs[0]->decl_kind, ModuleDeclKind::kProgram);
}

// =============================================================================
// §24.2 Program ports
// =============================================================================

TEST_F(ProgramTestParse, ProgramWithPorts) {
  auto* unit = Parse(
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
  auto* unit = Parse(
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
  auto* unit = Parse(
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
  auto* unit = Parse(
      "program p;\n"
      "  initial $display(\"init1\");\n"
      "  initial $display(\"init2\");\n"
      "endprogram\n");
  ASSERT_EQ(unit->programs.size(), 1u);
  int initial_count = 0;
  for (const auto* item : unit->programs[0]->items) {
    if (item->kind == ModuleItemKind::kInitialBlock) ++initial_count;
  }
  EXPECT_EQ(initial_count, 2);
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
// §24.5 $exit system task in programs
// =============================================================================

TEST_F(ProgramTestParse, ProgramWithExitCall) {
  auto* unit = Parse(
      "program p;\n"
      "  initial begin\n"
      "    $exit;\n"
      "  end\n"
      "endprogram\n");
  ASSERT_EQ(unit->programs.size(), 1u);
  ASSERT_EQ(unit->programs[0]->items.size(), 1u);
  EXPECT_EQ(unit->programs[0]->items[0]->kind, ModuleItemKind::kInitialBlock);
}

// =============================================================================
// §24.6 Program instantiation
// =============================================================================

TEST_F(ProgramTestParse, ProgramInstantiatedInModule) {
  auto* unit = Parse(
      "program test_prog(input logic clk);\n"
      "endprogram\n"
      "module top;\n"
      "  logic clk;\n"
      "  test_prog tp(.clk(clk));\n"
      "endmodule\n");
  ASSERT_EQ(unit->programs.size(), 1u);
  ASSERT_EQ(unit->modules.size(), 1u);
  bool found_inst = false;
  for (const auto* item : unit->modules[0]->items) {
    if (item->kind == ModuleItemKind::kModuleInst) {
      found_inst = true;
      EXPECT_EQ(item->inst_module, "test_prog");
      EXPECT_EQ(item->inst_name, "tp");
    }
  }
  EXPECT_TRUE(found_inst);
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

// =============================================================================
// §24.9 Program elaboration — program as top-level target
// =============================================================================

TEST(ProgramElab, ElaborateProgramWithVars) {
  ProgramElabFixture f;
  auto* design = ElaborateSource(
      "program my_prog;\n"
      "  logic [7:0] data;\n"
      "  assign data = 8'hAB;\n"
      "endprogram\n",
      f, "my_prog");
  ASSERT_NE(design, nullptr);
  auto* mod = design->top_modules[0];
  EXPECT_EQ(mod->name, "my_prog");
  EXPECT_FALSE(mod->variables.empty());
  EXPECT_FALSE(mod->assigns.empty());
}

TEST(ProgramElab, ElaborateProgramWithPorts) {
  ProgramElabFixture f;
  auto* design = ElaborateSource(
      "program prog_ports(input logic clk, input logic rst);\n"
      "endprogram\n",
      f, "prog_ports");
  ASSERT_NE(design, nullptr);
  auto* mod = design->top_modules[0];
  ASSERT_GE(mod->ports.size(), 2u);
  EXPECT_EQ(mod->ports[0].name, "clk");
  EXPECT_EQ(mod->ports[1].name, "rst");
}

TEST(ProgramElab, ElaborateProgramWithInitialBlock) {
  ProgramElabFixture f;
  auto* design = ElaborateSource(
      "program prog_init;\n"
      "  initial begin\n"
      "    $display(\"hello\");\n"
      "  end\n"
      "endprogram\n",
      f, "prog_init");
  ASSERT_NE(design, nullptr);
  auto* mod = design->top_modules[0];
  EXPECT_FALSE(mod->processes.empty());
  EXPECT_EQ(mod->processes[0].kind, RtlirProcessKind::kInitial);
}

// =============================================================================
// §24.10 Program instantiation via elaboration
// =============================================================================

TEST(ProgramElab, ProgramInstantiatedFromModule) {
  ProgramElabFixture f;
  auto* design = ElaborateSource(
      "program sub_prog(input logic a);\n"
      "endprogram\n"
      "module top;\n"
      "  logic sig;\n"
      "  sub_prog u0(.a(sig));\n"
      "endmodule\n",
      f, "top");
  ASSERT_NE(design, nullptr);
  auto* mod = design->top_modules[0];
  ASSERT_EQ(mod->children.size(), 1u);
  EXPECT_NE(mod->children[0].resolved, nullptr);
  EXPECT_EQ(mod->children[0].resolved->name, "sub_prog");
}

// =============================================================================
// §24.11 Reactive region context flag
// =============================================================================

TEST(ProgramSim, ReactiveContextFlag) {
  SourceManager mgr;
  Arena arena;
  Scheduler scheduler{arena};
  DiagEngine diag{mgr};
  SimContext ctx{scheduler, arena, diag};

  // No current process => not reactive.
  EXPECT_FALSE(ctx.IsReactiveContext());

  // Process with is_reactive = true => reactive context.
  Process proc;
  proc.is_reactive = true;
  ctx.SetCurrentProcess(&proc);
  EXPECT_TRUE(ctx.IsReactiveContext());

  // Process with is_reactive = false => not reactive.
  Process non_reactive;
  non_reactive.is_reactive = false;
  ctx.SetCurrentProcess(&non_reactive);
  EXPECT_FALSE(ctx.IsReactiveContext());

  ctx.SetCurrentProcess(nullptr);
}

// =============================================================================
// §24.12 Program with final block
// =============================================================================

TEST_F(ProgramTestParse, ProgramWithFinalBlock) {
  auto* unit = Parse(
      "program p;\n"
      "  final begin\n"
      "    $display(\"done\");\n"
      "  end\n"
      "endprogram\n");
  ASSERT_EQ(unit->programs.size(), 1u);
  ASSERT_EQ(unit->programs[0]->items.size(), 1u);
  EXPECT_EQ(unit->programs[0]->items[0]->kind, ModuleItemKind::kFinalBlock);
}

// =============================================================================
// §24.13 Program with import
// =============================================================================

TEST_F(ProgramTestParse, ProgramWithImport) {
  auto* unit = Parse(
      "program p;\n"
      "  import pkg::*;\n"
      "endprogram\n");
  ASSERT_EQ(unit->programs.size(), 1u);
  ASSERT_EQ(unit->programs[0]->items.size(), 1u);
  EXPECT_EQ(unit->programs[0]->items[0]->kind, ModuleItemKind::kImportDecl);
  EXPECT_TRUE(unit->programs[0]->items[0]->import_item.is_wildcard);
}

}  // namespace
