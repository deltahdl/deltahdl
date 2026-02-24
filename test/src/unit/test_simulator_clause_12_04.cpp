// §12.4: Conditional if–else statement

#include <gtest/gtest.h>

#include "common/arena.h"
#include "common/diagnostic.h"
#include "common/source_mgr.h"
#include "parser/ast.h"
#include "simulation/compiled_sim.h"
#include "simulation/sim_context.h"

using namespace delta;

struct CompiledSimFixture {
  SourceManager mgr;
  Arena arena;
  Scheduler scheduler{arena};
  DiagEngine diag{mgr};
  SimContext ctx{scheduler, arena, diag};
};
namespace {

TEST(CompiledSim, ExecuteIfElse) {
  CompiledSimFixture f;
  auto *sel = f.ctx.CreateVariable("sel", 1);
  sel->value = MakeLogic4VecVal(f.arena, 1, 1);
  auto *out = f.ctx.CreateVariable("out", 32);
  out->value = MakeLogic4VecVal(f.arena, 32, 0);

  // AST: if (sel) out = 1; else out = 0;
  auto *cond = f.arena.Create<Expr>();
  cond->kind = ExprKind::kIdentifier;
  cond->text = "sel";

  auto *then_lhs = f.arena.Create<Expr>();
  then_lhs->kind = ExprKind::kIdentifier;
  then_lhs->text = "out";
  auto *one = f.arena.Create<Expr>();
  one->kind = ExprKind::kIntegerLiteral;
  one->int_val = 1;
  auto *then_stmt = f.arena.Create<Stmt>();
  then_stmt->kind = StmtKind::kBlockingAssign;
  then_stmt->lhs = then_lhs;
  then_stmt->rhs = one;

  auto *else_lhs = f.arena.Create<Expr>();
  else_lhs->kind = ExprKind::kIdentifier;
  else_lhs->text = "out";
  auto *zero = f.arena.Create<Expr>();
  zero->kind = ExprKind::kIntegerLiteral;
  zero->int_val = 0;
  auto *else_stmt = f.arena.Create<Stmt>();
  else_stmt->kind = StmtKind::kBlockingAssign;
  else_stmt->lhs = else_lhs;
  else_stmt->rhs = zero;

  auto *if_stmt = f.arena.Create<Stmt>();
  if_stmt->kind = StmtKind::kIf;
  if_stmt->condition = cond;
  if_stmt->then_branch = then_stmt;
  if_stmt->else_branch = else_stmt;

  auto *block = f.arena.Create<Stmt>();
  block->kind = StmtKind::kBlock;
  block->stmts.push_back(if_stmt);

  auto compiled = ProcessCompiler::Compile(1, block);
  compiled.Execute(f.ctx);
  EXPECT_EQ(out->value.ToUint64(), 1u);

  // Change sel to 0, re-execute.
  sel->value = MakeLogic4VecVal(f.arena, 1, 0);
  compiled.Execute(f.ctx);
  EXPECT_EQ(out->value.ToUint64(), 0u);
}

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

}  // namespace
