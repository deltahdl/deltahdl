#include <gtest/gtest.h>

#include <string>

#include "common/arena.h"
#include "common/diagnostic.h"
#include "common/source_mgr.h"
#include "elaboration/elaborator.h"
#include "elaboration/rtlir.h"
#include "lexer/lexer.h"
#include "parser/parser.h"
#include "simulation/lowerer.h"
#include "simulation/scheduler.h"
#include "simulation/sim_context.h"
#include "simulation/variable.h"

using namespace delta;

namespace {

struct SimA606Fixture {
  SourceManager mgr;
  Arena arena;
  Scheduler scheduler{arena};
  DiagEngine diag{mgr};
  SimContext ctx{scheduler, arena, diag};
};

static RtlirDesign *ElaborateSrc(const std::string &src, SimA606Fixture &f) {
  auto fid = f.mgr.AddFile("<test>", src);
  Lexer lexer(f.mgr.FileContent(fid), fid, f.diag);
  Parser parser(lexer, f.arena, f.diag);
  auto *cu = parser.Parse();
  Elaborator elab(f.arena, f.diag, cu);
  return elab.Elaborate(cu->modules.back()->name);
}

}  // namespace

// =============================================================================
// Simulation: conditional statement execution
// =============================================================================
// §12.4: if true takes then branch
TEST(SimA606, IfTrueTakesThenBranch) {
  SimA606Fixture f;
  auto *design = ElaborateSrc(
      "module t;\n"
      "  logic [7:0] x;\n"
      "  initial begin\n"
      "    if (1) x = 8'd42;\n"
      "    else x = 8'd99;\n"
      "  end\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  Lowerer lowerer(f.ctx, f.arena, f.diag);
  lowerer.Lower(design);
  f.scheduler.Run();
  auto *var = f.ctx.FindVariable("x");
  ASSERT_NE(var, nullptr);
  EXPECT_EQ(var->value.ToUint64(), 42u);
}

// §12.4: if false takes else branch
TEST(SimA606, IfFalseTakesElseBranch) {
  SimA606Fixture f;
  auto *design = ElaborateSrc(
      "module t;\n"
      "  logic [7:0] x;\n"
      "  initial begin\n"
      "    if (0) x = 8'd42;\n"
      "    else x = 8'd99;\n"
      "  end\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  Lowerer lowerer(f.ctx, f.arena, f.diag);
  lowerer.Lower(design);
  f.scheduler.Run();
  auto *var = f.ctx.FindVariable("x");
  ASSERT_NE(var, nullptr);
  EXPECT_EQ(var->value.ToUint64(), 99u);
}

// §12.4: if false with no else — no change
TEST(SimA606, IfFalseNoElse) {
  SimA606Fixture f;
  auto *design = ElaborateSrc(
      "module t;\n"
      "  logic [7:0] x;\n"
      "  initial begin\n"
      "    x = 8'd10;\n"
      "    if (0) x = 8'd42;\n"
      "  end\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  Lowerer lowerer(f.ctx, f.arena, f.diag);
  lowerer.Lower(design);
  f.scheduler.Run();
  auto *var = f.ctx.FindVariable("x");
  ASSERT_NE(var, nullptr);
  EXPECT_EQ(var->value.ToUint64(), 10u);
}

// §12.4.1: if-else-if chain selects correct branch
TEST(SimA606, IfElseIfChainSelectsCorrectBranch) {
  SimA606Fixture f;
  auto *design = ElaborateSrc(
      "module t;\n"
      "  logic [7:0] a, x;\n"
      "  initial begin\n"
      "    a = 8'd2;\n"
      "    if (a == 8'd0) x = 8'd10;\n"
      "    else if (a == 8'd1) x = 8'd20;\n"
      "    else if (a == 8'd2) x = 8'd30;\n"
      "    else x = 8'd40;\n"
      "  end\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  Lowerer lowerer(f.ctx, f.arena, f.diag);
  lowerer.Lower(design);
  f.scheduler.Run();
  auto *var = f.ctx.FindVariable("x");
  ASSERT_NE(var, nullptr);
  EXPECT_EQ(var->value.ToUint64(), 30u);
}

// §12.4.1: if-else-if chain falls through to final else
TEST(SimA606, IfElseIfFallsToElse) {
  SimA606Fixture f;
  auto *design = ElaborateSrc(
      "module t;\n"
      "  logic [7:0] a, x;\n"
      "  initial begin\n"
      "    a = 8'd5;\n"
      "    if (a == 8'd0) x = 8'd10;\n"
      "    else if (a == 8'd1) x = 8'd20;\n"
      "    else x = 8'd99;\n"
      "  end\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  Lowerer lowerer(f.ctx, f.arena, f.diag);
  lowerer.Lower(design);
  f.scheduler.Run();
  auto *var = f.ctx.FindVariable("x");
  ASSERT_NE(var, nullptr);
  EXPECT_EQ(var->value.ToUint64(), 99u);
}

// §12.4: nonzero value is truthy
TEST(SimA606, IfNonzeroIsTruthy) {
  SimA606Fixture f;
  auto *design = ElaborateSrc(
      "module t;\n"
      "  logic [7:0] x;\n"
      "  initial begin\n"
      "    if (8'd255) x = 8'd1;\n"
      "    else x = 8'd0;\n"
      "  end\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  Lowerer lowerer(f.ctx, f.arena, f.diag);
  lowerer.Lower(design);
  f.scheduler.Run();
  auto *var = f.ctx.FindVariable("x");
  ASSERT_NE(var, nullptr);
  EXPECT_EQ(var->value.ToUint64(), 1u);
}

// §12.4: nested if — both levels evaluated
TEST(SimA606, NestedIfBothLevels) {
  SimA606Fixture f;
  auto *design = ElaborateSrc(
      "module t;\n"
      "  logic [7:0] x;\n"
      "  initial begin\n"
      "    if (1) begin\n"
      "      if (1) x = 8'd77;\n"
      "      else x = 8'd88;\n"
      "    end else begin\n"
      "      x = 8'd99;\n"
      "    end\n"
      "  end\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  Lowerer lowerer(f.ctx, f.arena, f.diag);
  lowerer.Lower(design);
  f.scheduler.Run();
  auto *var = f.ctx.FindVariable("x");
  ASSERT_NE(var, nullptr);
  EXPECT_EQ(var->value.ToUint64(), 77u);
}

// §12.4: nested if — outer true, inner false takes inner else
TEST(SimA606, NestedIfOuterTrueInnerFalse) {
  SimA606Fixture f;
  auto *design = ElaborateSrc(
      "module t;\n"
      "  logic [7:0] x;\n"
      "  initial begin\n"
      "    if (1) begin\n"
      "      if (0) x = 8'd77;\n"
      "      else x = 8'd88;\n"
      "    end else begin\n"
      "      x = 8'd99;\n"
      "    end\n"
      "  end\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  Lowerer lowerer(f.ctx, f.arena, f.diag);
  lowerer.Lower(design);
  f.scheduler.Run();
  auto *var = f.ctx.FindVariable("x");
  ASSERT_NE(var, nullptr);
  EXPECT_EQ(var->value.ToUint64(), 88u);
}

// §12.4.2: unique if — qualifier stored on AST
TEST(SimA606, UniqueIfQualifierStored) {
  SimA606Fixture f;
  auto *design = ElaborateSrc(
      "module t;\n"
      "  logic [7:0] a, x;\n"
      "  initial begin\n"
      "    a = 8'd1;\n"
      "    unique if (a == 8'd0) x = 8'd10;\n"
      "    else if (a == 8'd1) x = 8'd20;\n"
      "    else x = 8'd30;\n"
      "  end\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  Lowerer lowerer(f.ctx, f.arena, f.diag);
  lowerer.Lower(design);
  f.scheduler.Run();
  auto *var = f.ctx.FindVariable("x");
  ASSERT_NE(var, nullptr);
  EXPECT_EQ(var->value.ToUint64(), 20u);
}

// §12.4.2: priority if — executes first matching branch
TEST(SimA606, PriorityIfFirstMatch) {
  SimA606Fixture f;
  auto *design = ElaborateSrc(
      "module t;\n"
      "  logic [7:0] x;\n"
      "  initial begin\n"
      "    priority if (1) x = 8'd10;\n"
      "    else if (1) x = 8'd20;\n"
      "    else x = 8'd30;\n"
      "  end\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  Lowerer lowerer(f.ctx, f.arena, f.diag);
  lowerer.Lower(design);
  f.scheduler.Run();
  auto *var = f.ctx.FindVariable("x");
  ASSERT_NE(var, nullptr);
  EXPECT_EQ(var->value.ToUint64(), 10u);
}

// §12.4: if inside for loop
TEST(SimA606, IfInsideForLoop) {
  SimA606Fixture f;
  auto *design = ElaborateSrc(
      "module t;\n"
      "  logic [7:0] count;\n"
      "  initial begin\n"
      "    count = 8'd0;\n"
      "    for (int i = 0; i < 5; i = i + 1) begin\n"
      "      if (i > 2) count = count + 8'd1;\n"
      "    end\n"
      "  end\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  Lowerer lowerer(f.ctx, f.arena, f.diag);
  lowerer.Lower(design);
  f.scheduler.Run();
  auto *var = f.ctx.FindVariable("count");
  ASSERT_NE(var, nullptr);
  EXPECT_EQ(var->value.ToUint64(), 2u);  // i=3 and i=4
}

// §12.4: sequential if statements (not chained)
TEST(SimA606, SequentialIfStatements) {
  SimA606Fixture f;
  auto *design = ElaborateSrc(
      "module t;\n"
      "  logic [7:0] x;\n"
      "  initial begin\n"
      "    x = 8'd0;\n"
      "    if (1) x = x + 8'd1;\n"
      "    if (1) x = x + 8'd2;\n"
      "    if (0) x = x + 8'd4;\n"
      "  end\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  Lowerer lowerer(f.ctx, f.arena, f.diag);
  lowerer.Lower(design);
  f.scheduler.Run();
  auto *var = f.ctx.FindVariable("x");
  ASSERT_NE(var, nullptr);
  EXPECT_EQ(var->value.ToUint64(), 3u);  // 0 + 1 + 2 = 3
}
