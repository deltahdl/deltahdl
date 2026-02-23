// §11.11: Minimum, typical, and maximum delay expressions

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

static Expr* MakeUnary(Arena& arena, TokenKind op, Expr* operand) {
  auto* e = arena.Create<Expr>();
  e->kind = ExprKind::kUnary;
  e->op = op;
  e->lhs = operand;
  return e;
}

static Expr* MakeBinary(Arena& arena, TokenKind op, Expr* lhs, Expr* rhs) {
  auto* e = arena.Create<Expr>();
  e->kind = ExprKind::kBinary;
  e->op = op;
  e->lhs = lhs;
  e->rhs = rhs;
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

static Variable* MakeRealVar(EvalOpXZFixture& f, std::string_view name,
                             double val) {
  auto* var = f.ctx.CreateVariable(name, 64);
  uint64_t bits = 0;
  std::memcpy(&bits, &val, sizeof(double));
  var->value = MakeLogic4VecVal(f.arena, 64, bits);
  var->value.is_real = true;
  f.ctx.RegisterRealVariable(name);
  return var;
}

static double ToDouble(const Logic4Vec& v) {
  double d = 0.0;
  uint64_t bits = v.ToUint64();
  std::memcpy(&d, &bits, sizeof(double));
  return d;
}

static std::string VecToStr(const Logic4Vec& vec) {
  std::string result;
  uint32_t nbytes = vec.width / 8;
  for (uint32_t i = nbytes; i > 0; --i) {
    uint32_t byte_idx = i - 1;
    uint32_t word = (byte_idx * 8) / 64;
    uint32_t bit = (byte_idx * 8) % 64;
    auto ch = static_cast<char>((vec.words[word].aval >> bit) & 0xFF);
    result.push_back(ch);
  }
  return result;
}

static Variable* MakeStringVar(EvalOpXZFixture& f, std::string_view name,
                               std::string_view value) {
  uint32_t width = static_cast<uint32_t>(value.size()) * 8;
  if (width == 0) width = 8;
  auto* var = f.ctx.CreateVariable(name, width);
  var->value = MakeLogic4Vec(f.arena, width);
  for (size_t i = 0; i < value.size(); ++i) {
    auto byte_idx = static_cast<uint32_t>(value.size() - 1 - i);
    uint32_t word = (byte_idx * 8) / 64;
    uint32_t bit = (byte_idx * 8) % 64;
    var->value.words[word].aval |=
        static_cast<uint64_t>(static_cast<unsigned char>(value[i])) << bit;
  }
  f.ctx.RegisterStringVariable(name);
  return var;
}

namespace {

// ==========================================================================
// MinTypMax evaluation — §11.11
// ==========================================================================
TEST(EvalOpXZ, MinTypMaxDefaultTyp) {
  EvalOpXZFixture f;
  // Default delay mode is typ — should return middle expression.
  auto* mtm = f.arena.Create<Expr>();
  mtm->kind = ExprKind::kMinTypMax;
  mtm->lhs = MakeInt(f.arena, 10);        // min
  mtm->condition = MakeInt(f.arena, 20);  // typ
  mtm->rhs = MakeInt(f.arena, 30);        // max
  auto result = EvalExpr(mtm, f.ctx, f.arena);
  EXPECT_EQ(result.ToUint64(), 20u);
}

TEST(EvalOpXZ, MinTypMaxMin) {
  EvalOpXZFixture f;
  f.ctx.SetDelayMode(DelayMode::kMin);
  auto* mtm = f.arena.Create<Expr>();
  mtm->kind = ExprKind::kMinTypMax;
  mtm->lhs = MakeInt(f.arena, 10);
  mtm->condition = MakeInt(f.arena, 20);
  mtm->rhs = MakeInt(f.arena, 30);
  auto result = EvalExpr(mtm, f.ctx, f.arena);
  EXPECT_EQ(result.ToUint64(), 10u);
}

TEST(EvalOpXZ, MinTypMaxMax) {
  EvalOpXZFixture f;
  f.ctx.SetDelayMode(DelayMode::kMax);
  auto* mtm = f.arena.Create<Expr>();
  mtm->kind = ExprKind::kMinTypMax;
  mtm->lhs = MakeInt(f.arena, 10);
  mtm->condition = MakeInt(f.arena, 20);
  mtm->rhs = MakeInt(f.arena, 30);
  auto result = EvalExpr(mtm, f.ctx, f.arena);
  EXPECT_EQ(result.ToUint64(), 30u);
}

}  // namespace
