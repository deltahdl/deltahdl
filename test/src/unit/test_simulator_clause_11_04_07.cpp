// §11.4.7: Logical operators

#include <gtest/gtest.h>

#include "common/arena.h"
#include "common/diagnostic.h"
#include "common/source_mgr.h"
#include "lexer/token.h"
#include "parser/ast.h"
#include "simulation/eval.h"
#include "simulation/sim_context.h"

using namespace delta;

// Shared fixture for expression evaluation tests.
struct EvalOpFixture {
  SourceManager mgr;
  Arena arena;
  Scheduler scheduler{arena};
  DiagEngine diag{mgr};
  SimContext ctx{scheduler, arena, diag};
};

// Helper: build a simple integer literal Expr node.
static Expr *MakeInt(Arena &arena, uint64_t val) {
  auto *e = arena.Create<Expr>();
  e->kind = ExprKind::kIntegerLiteral;
  e->int_val = val;
  return e;
}

// Helper: build an identifier Expr node.
static Expr *MakeId(Arena &arena, std::string_view name) {
  auto *e = arena.Create<Expr>();
  e->kind = ExprKind::kIdentifier;
  e->text = name;
  return e;
}

// Helper: build a binary Expr.
static Expr *MakeBinary(Arena &arena, TokenKind op, Expr *lhs, Expr *rhs) {
  auto *e = arena.Create<Expr>();
  e->kind = ExprKind::kBinary;
  e->op = op;
  e->lhs = lhs;
  e->rhs = rhs;
  return e;
}

namespace {

TEST(EvalOp, AmpEq) {
  EvalOpFixture f;
  auto *var = f.ctx.CreateVariable("a", 32);
  var->value = MakeLogic4VecVal(f.arena, 32, 0xFF);

  auto *expr = MakeBinary(f.arena, TokenKind::kAmpEq, MakeId(f.arena, "a"),
                          MakeInt(f.arena, 0x0F));
  auto result = EvalExpr(expr, f.ctx, f.arena);
  EXPECT_EQ(result.ToUint64(), 0x0Fu);
  EXPECT_EQ(var->value.ToUint64(), 0x0Fu);
}

TEST(EvalOp, PipeEq) {
  EvalOpFixture f;
  auto *var = f.ctx.CreateVariable("a", 32);
  var->value = MakeLogic4VecVal(f.arena, 32, 0xF0);

  auto *expr = MakeBinary(f.arena, TokenKind::kPipeEq, MakeId(f.arena, "a"),
                          MakeInt(f.arena, 0x0F));
  auto result = EvalExpr(expr, f.ctx, f.arena);
  EXPECT_EQ(result.ToUint64(), 0xFFu);
  EXPECT_EQ(var->value.ToUint64(), 0xFFu);
}

TEST(EvalOp, CaretEq) {
  EvalOpFixture f;
  auto *var = f.ctx.CreateVariable("a", 32);
  var->value = MakeLogic4VecVal(f.arena, 32, 0xFF);

  auto *expr = MakeBinary(f.arena, TokenKind::kCaretEq, MakeId(f.arena, "a"),
                          MakeInt(f.arena, 0x0F));
  auto result = EvalExpr(expr, f.ctx, f.arena);
  EXPECT_EQ(result.ToUint64(), 0xF0u);
  EXPECT_EQ(var->value.ToUint64(), 0xF0u);
}

// Shared fixture for expression evaluation tests.
struct EvalOpXZFixture {
  SourceManager mgr;
  Arena arena;
  Scheduler scheduler{arena};
  DiagEngine diag{mgr};
  SimContext ctx{scheduler, arena, diag};
};

static Expr *MakeUnary(Arena &arena, TokenKind op, Expr *operand) {
  auto *e = arena.Create<Expr>();
  e->kind = ExprKind::kUnary;
  e->op = op;
  e->lhs = operand;
  return e;
}

static Variable *MakeVar4(EvalOpXZFixture &f, std::string_view name,
                          uint32_t width, uint64_t aval, uint64_t bval) {
  auto *var = f.ctx.CreateVariable(name, width);
  var->value = MakeLogic4Vec(f.arena, width);
  var->value.words[0].aval = aval;
  var->value.words[0].bval = bval;
  return var;
}

// ==========================================================================
// Logical operator X/Z — §11.4.7
// ==========================================================================
TEST(EvalOpXZ, LogicalNotX) {
  EvalOpXZFixture f;
  // !4'b1x00 → x
  MakeVar4(f, "ln", 4, 0b1000, 0b0100);
  auto *expr = MakeUnary(f.arena, TokenKind::kBang, MakeId(f.arena, "ln"));
  auto result = EvalExpr(expr, f.ctx, f.arena);
  EXPECT_NE(result.words[0].bval, 0u);
}

TEST(EvalOpXZ, LogicalAndZeroX) {
  EvalOpXZFixture f;
  // 0 && x → 0 (short-circuit: lhs known-0 → result 0)
  MakeVar4(f, "lx", 4, 0b0000, 0b0100);
  auto *expr = MakeBinary(f.arena, TokenKind::kAmpAmp, MakeInt(f.arena, 0),
                          MakeId(f.arena, "lx"));
  auto result = EvalExpr(expr, f.ctx, f.arena);
  EXPECT_EQ(result.ToUint64(), 0u);
  EXPECT_EQ(result.words[0].bval, 0u);
}

TEST(EvalOpXZ, LogicalAndXZero) {
  EvalOpXZFixture f;
  // x && 0 → 0 (rhs known-0 → result 0 despite lhs unknown)
  MakeVar4(f, "ax", 4, 0b0000, 0b0100);
  auto *expr = MakeBinary(f.arena, TokenKind::kAmpAmp, MakeId(f.arena, "ax"),
                          MakeInt(f.arena, 0));
  auto result = EvalExpr(expr, f.ctx, f.arena);
  EXPECT_EQ(result.ToUint64(), 0u);
  EXPECT_EQ(result.words[0].bval, 0u);
}

TEST(EvalOpXZ, LogicalAndXX) {
  EvalOpXZFixture f;
  // x && 1 → x
  MakeVar4(f, "bx", 4, 0b0000, 0b0100);
  auto *expr = MakeBinary(f.arena, TokenKind::kAmpAmp, MakeId(f.arena, "bx"),
                          MakeInt(f.arena, 1));
  auto result = EvalExpr(expr, f.ctx, f.arena);
  EXPECT_NE(result.words[0].bval, 0u);
}

TEST(EvalOpXZ, LogicalOrOneX) {
  EvalOpXZFixture f;
  // 1 || x → 1 (short-circuit: lhs known-1 → result 1)
  MakeVar4(f, "ox", 4, 0b0000, 0b0100);
  auto *expr = MakeBinary(f.arena, TokenKind::kPipePipe, MakeInt(f.arena, 1),
                          MakeId(f.arena, "ox"));
  auto result = EvalExpr(expr, f.ctx, f.arena);
  EXPECT_EQ(result.ToUint64(), 1u);
  EXPECT_EQ(result.words[0].bval, 0u);
}

TEST(EvalOpXZ, LogicalOrXOne) {
  EvalOpXZFixture f;
  // x || 1 → 1
  MakeVar4(f, "px", 4, 0b0000, 0b0100);
  auto *expr = MakeBinary(f.arena, TokenKind::kPipePipe, MakeId(f.arena, "px"),
                          MakeInt(f.arena, 1));
  auto result = EvalExpr(expr, f.ctx, f.arena);
  EXPECT_EQ(result.ToUint64(), 1u);
  EXPECT_EQ(result.words[0].bval, 0u);
}

TEST(EvalOpXZ, LogicalOrXX) {
  EvalOpXZFixture f;
  // x || 0 → x
  MakeVar4(f, "qx", 4, 0b0000, 0b0100);
  auto *expr = MakeBinary(f.arena, TokenKind::kPipePipe, MakeId(f.arena, "qx"),
                          MakeInt(f.arena, 0));
  auto result = EvalExpr(expr, f.ctx, f.arena);
  EXPECT_NE(result.words[0].bval, 0u);
}

// Signed comparison, signed arithmetic, expression type rules
// moved to test_eval_advanced.cpp
// ==========================================================================
// Logical implication (->) and equivalence (<->) — §11.4.7
// ==========================================================================
TEST(EvalOpXZ, ImplTT) {
  EvalOpXZFixture f;
  // 1 -> 1 = 1
  MakeVar4(f, "it1", 1, 1, 0);
  MakeVar4(f, "it2", 1, 1, 0);
  auto *expr = MakeBinary(f.arena, TokenKind::kArrow, MakeId(f.arena, "it1"),
                          MakeId(f.arena, "it2"));
  auto result = EvalExpr(expr, f.ctx, f.arena);
  EXPECT_EQ(result.width, 1u);
  EXPECT_EQ(result.ToUint64(), 1u);
}

TEST(EvalOpXZ, ImplTF) {
  EvalOpXZFixture f;
  // 1 -> 0 = 0
  MakeVar4(f, "it1", 1, 1, 0);
  MakeVar4(f, "it2", 1, 0, 0);
  auto *expr = MakeBinary(f.arena, TokenKind::kArrow, MakeId(f.arena, "it1"),
                          MakeId(f.arena, "it2"));
  auto result = EvalExpr(expr, f.ctx, f.arena);
  EXPECT_EQ(result.ToUint64(), 0u);
}

TEST(EvalOpXZ, ImplFT) {
  EvalOpXZFixture f;
  // 0 -> 1 = 1 (vacuous truth)
  MakeVar4(f, "it1", 1, 0, 0);
  MakeVar4(f, "it2", 1, 1, 0);
  auto *expr = MakeBinary(f.arena, TokenKind::kArrow, MakeId(f.arena, "it1"),
                          MakeId(f.arena, "it2"));
  auto result = EvalExpr(expr, f.ctx, f.arena);
  EXPECT_EQ(result.ToUint64(), 1u);
}

TEST(EvalOpXZ, ImplFF) {
  EvalOpXZFixture f;
  // 0 -> 0 = 1 (vacuous truth)
  MakeVar4(f, "it1", 1, 0, 0);
  MakeVar4(f, "it2", 1, 0, 0);
  auto *expr = MakeBinary(f.arena, TokenKind::kArrow, MakeId(f.arena, "it1"),
                          MakeId(f.arena, "it2"));
  auto result = EvalExpr(expr, f.ctx, f.arena);
  EXPECT_EQ(result.ToUint64(), 1u);
}

TEST(EvalOpXZ, ImplXT) {
  EvalOpXZFixture f;
  // x -> 1 = 1 (since !x || 1 = 1 regardless of x)
  MakeVar4(f, "ix1", 1, 0, 1);  // 1'bx
  MakeVar4(f, "ix2", 1, 1, 0);
  auto *expr = MakeBinary(f.arena, TokenKind::kArrow, MakeId(f.arena, "ix1"),
                          MakeId(f.arena, "ix2"));
  auto result = EvalExpr(expr, f.ctx, f.arena);
  EXPECT_EQ(result.ToUint64(), 1u);
  EXPECT_EQ(result.words[0].bval, 0u);
}

TEST(EvalOpXZ, ImplXF) {
  EvalOpXZFixture f;
  // x -> 0 = x (since !x || 0 = !x, and !x is x when x is unknown)
  MakeVar4(f, "ix1", 1, 0, 1);  // 1'bx
  MakeVar4(f, "ix2", 1, 0, 0);
  auto *expr = MakeBinary(f.arena, TokenKind::kArrow, MakeId(f.arena, "ix1"),
                          MakeId(f.arena, "ix2"));
  auto result = EvalExpr(expr, f.ctx, f.arena);
  EXPECT_NE(result.words[0].bval, 0u);  // result is x
}

TEST(EvalOpXZ, EquivSame) {
  EvalOpXZFixture f;
  // 1 <-> 1 = 1
  MakeVar4(f, "eq1", 1, 1, 0);
  MakeVar4(f, "eq2", 1, 1, 0);
  auto *expr = MakeBinary(f.arena, TokenKind::kLtDashGt, MakeId(f.arena, "eq1"),
                          MakeId(f.arena, "eq2"));
  auto result = EvalExpr(expr, f.ctx, f.arena);
  EXPECT_EQ(result.ToUint64(), 1u);
}

TEST(EvalOpXZ, EquivDiff) {
  EvalOpXZFixture f;
  // 1 <-> 0 = 0
  MakeVar4(f, "eq1", 1, 1, 0);
  MakeVar4(f, "eq2", 1, 0, 0);
  auto *expr = MakeBinary(f.arena, TokenKind::kLtDashGt, MakeId(f.arena, "eq1"),
                          MakeId(f.arena, "eq2"));
  auto result = EvalExpr(expr, f.ctx, f.arena);
  EXPECT_EQ(result.ToUint64(), 0u);
}

TEST(EvalOpXZ, EquivX) {
  EvalOpXZFixture f;
  // x <-> 1 = x
  MakeVar4(f, "ex1", 1, 0, 1);  // 1'bx
  MakeVar4(f, "ex2", 1, 1, 0);
  auto *expr = MakeBinary(f.arena, TokenKind::kLtDashGt, MakeId(f.arena, "ex1"),
                          MakeId(f.arena, "ex2"));
  auto result = EvalExpr(expr, f.ctx, f.arena);
  EXPECT_NE(result.words[0].bval, 0u);  // result is x
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

// § expression — logical AND
TEST(SimA83, LogicalAnd) {
  SimA83Fixture f;
  auto *design = ElaborateSrc(
      "module t;\n"
      "  logic x;\n"
      "  initial x = (8'd1 && 8'd1);\n"
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

// § expression — logical OR
TEST(SimA83, LogicalOr) {
  SimA83Fixture f;
  auto *design = ElaborateSrc(
      "module t;\n"
      "  logic x;\n"
      "  initial x = (8'd0 || 8'd1);\n"
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

}  // namespace
