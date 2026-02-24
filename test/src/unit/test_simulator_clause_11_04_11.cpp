// §11.4.11: Conditional operator

#include <gtest/gtest.h>

#include <cstring>

#include "common/arena.h"
#include "common/diagnostic.h"
#include "common/source_mgr.h"
#include "lexer/token.h"
#include "parser/ast.h"
#include "simulation/eval.h"
#include "simulation/sim_context.h"

using namespace delta;

// Shared fixture for expression evaluation tests.
struct EvalOpXZFixture {
  SourceManager mgr;
  Arena arena;
  Scheduler scheduler{arena};
  DiagEngine diag{mgr};
  SimContext ctx{scheduler, arena, diag};
};

static Expr* MakeInt(Arena& arena, uint64_t val) {
  auto* e = arena.Create<Expr>();
  e->kind = ExprKind::kIntegerLiteral;
  e->int_val = val;
  return e;
}

static Expr* MakeId(Arena& arena, std::string_view name) {
  auto* e = arena.Create<Expr>();
  e->kind = ExprKind::kIdentifier;
  e->text = name;
  return e;
}

static Variable* MakeVar4(EvalOpXZFixture& f, std::string_view name,
                          uint32_t width, uint64_t aval, uint64_t bval) {
  auto* var = f.ctx.CreateVariable(name, width);
  var->value = MakeLogic4Vec(f.arena, width);
  var->value.words[0].aval = aval;
  var->value.words[0].bval = bval;
  return var;
}

namespace {

// ==========================================================================
// Ternary X/Z condition — §11.4.11
// ==========================================================================
TEST(EvalOpXZ, TernaryZCond) {
  EvalOpXZFixture f;
  // z ? 4'b1100 : 4'b1010 → same as x condition (bit-by-bit combine)
  MakeVar4(f, "tz", 1, 0, 1);  // 1'bz (aval=0, bval=1)
  auto* tv = f.ctx.CreateVariable("zt", 4);
  tv->value = MakeLogic4VecVal(f.arena, 4, 0b1100);
  auto* fv = f.ctx.CreateVariable("zf", 4);
  fv->value = MakeLogic4VecVal(f.arena, 4, 0b1010);
  auto* ternary = f.arena.Create<Expr>();
  ternary->kind = ExprKind::kTernary;
  ternary->condition = MakeId(f.arena, "tz");
  ternary->true_expr = MakeId(f.arena, "zt");
  ternary->false_expr = MakeId(f.arena, "zf");
  auto result = EvalExpr(ternary, f.ctx, f.arena);
  // Same as TernaryXCondDiff: aval=0b1000, bval=0b0110
  EXPECT_EQ(result.words[0].aval, 0b1000u);
  EXPECT_EQ(result.words[0].bval, 0b0110u);
}

TEST(EvalOpXZ, TernaryXCondSame) {
  EvalOpXZFixture f;
  // x ? 5 : 5 → 5 (both branches same → known result)
  MakeVar4(f, "tc", 1, 0, 1);  // 1'bx
  auto* ternary = f.arena.Create<Expr>();
  ternary->kind = ExprKind::kTernary;
  ternary->condition = MakeId(f.arena, "tc");
  ternary->true_expr = MakeInt(f.arena, 5);
  ternary->false_expr = MakeInt(f.arena, 5);
  auto result = EvalExpr(ternary, f.ctx, f.arena);
  EXPECT_EQ(result.ToUint64(), 5u);
  EXPECT_EQ(result.words[0].bval, 0u);
}

TEST(EvalOpXZ, TernaryXCondDiff) {
  EvalOpXZFixture f;
  // x ? 4'b1100 : 4'b1010 → 4'b1x0x (matching bits kept, differing → X)
  MakeVar4(f, "td", 1, 0, 1);  // 1'bx
  auto* tv = f.ctx.CreateVariable("tt", 4);
  tv->value = MakeLogic4VecVal(f.arena, 4, 0b1100);
  auto* fv = f.ctx.CreateVariable("tf", 4);
  fv->value = MakeLogic4VecVal(f.arena, 4, 0b1010);
  auto* ternary = f.arena.Create<Expr>();
  ternary->kind = ExprKind::kTernary;
  ternary->condition = MakeId(f.arena, "td");
  ternary->true_expr = MakeId(f.arena, "tt");
  ternary->false_expr = MakeId(f.arena, "tf");
  auto result = EvalExpr(ternary, f.ctx, f.arena);
  // 4'b1x0x: bits that match keep value, bits that differ → X
  //   bit3: 1==1 → 1 (aval=1, bval=0)
  //   bit2: 1!=0 → x (aval=0, bval=1)
  //   bit1: 0!=1 → x (aval=0, bval=1)
  //   bit0: 0==0 → 0 (aval=0, bval=0)
  // aval=0b1000, bval=0b0110
  EXPECT_EQ(result.words[0].aval, 0b1000u);
  EXPECT_EQ(result.words[0].bval, 0b0110u);
}

struct SimA83Fixture {
  SourceManager mgr;
  Arena arena;
  Scheduler scheduler{arena};
  DiagEngine diag{mgr};
  SimContext ctx{scheduler, arena, diag};
};

static RtlirDesign *ElaborateSrc(const std::string &src, SimA83Fixture &f) {
  auto fid = f.mgr.AddFile("<test>", src);
  Lexer lexer(f.mgr.FileContent(fid), fid, f.diag);
  Parser parser(lexer, f.arena, f.diag);
  auto *cu = parser.Parse();
  Elaborator elab(f.arena, f.diag, cu);
  return elab.Elaborate(cu->modules.back()->name);
}

// § conditional_expression — ternary true branch
TEST(SimA83, TernaryTrueBranch) {
  SimA83Fixture f;
  auto *design = ElaborateSrc(
      "module t;\n"
      "  logic [7:0] x;\n"
      "  initial x = 1 ? 8'd10 : 8'd20;\n"
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

// § conditional_expression — ternary false branch
TEST(SimA83, TernaryFalseBranch) {
  SimA83Fixture f;
  auto *design = ElaborateSrc(
      "module t;\n"
      "  logic [7:0] x;\n"
      "  initial x = 0 ? 8'd10 : 8'd20;\n"
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

// § conditional_expression — nested ternary
TEST(SimA83, NestedTernary) {
  SimA83Fixture f;
  auto *design = ElaborateSrc(
      "module t;\n"
      "  logic [7:0] x;\n"
      "  initial x = 1 ? (0 ? 8'd1 : 8'd2) : 8'd3;\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  Lowerer lowerer(f.ctx, f.arena, f.diag);
  lowerer.Lower(design);
  f.scheduler.Run();
  auto *var = f.ctx.FindVariable("x");
  ASSERT_NE(var, nullptr);
  EXPECT_EQ(var->value.ToUint64(), 2u);
}

}  // namespace
