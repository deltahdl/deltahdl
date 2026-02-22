// §11.4.4: Relational operators

#include "common/arena.h"
#include "common/diagnostic.h"
#include "common/source_mgr.h"
#include "lexer/token.h"
#include "parser/ast.h"
#include "simulation/eval.h"
#include "simulation/sim_context.h" // StructTypeInfo, StructFieldInfo
#include <cstring>
#include <gtest/gtest.h>

using namespace delta;

// Shared fixture for advanced expression evaluation tests (§11 phases 22+).
struct EvalAdvFixture {
  SourceManager mgr;
  Arena arena;
  Scheduler scheduler{arena};
  DiagEngine diag{mgr};
  SimContext ctx{scheduler, arena, diag};
};

static Expr *MakeId(Arena &arena, std::string_view name) {
  auto *e = arena.Create<Expr>();
  e->kind = ExprKind::kIdentifier;
  e->text = name;
  return e;
}

static Variable *MakeVar(EvalAdvFixture &f, std::string_view name,
                         uint32_t width, uint64_t val) {
  auto *var = f.ctx.CreateVariable(name, width);
  var->value = MakeLogic4VecVal(f.arena, width, val);
  return var;
}

static Expr *MakeBinary(Arena &arena, TokenKind op, Expr *lhs, Expr *rhs) {
  auto *e = arena.Create<Expr>();
  e->kind = ExprKind::kBinary;
  e->op = op;
  e->lhs = lhs;
  e->rhs = rhs;
  return e;
}

static Variable *MakeSignedVarAdv(EvalAdvFixture &f, std::string_view name,
                                  uint32_t width, uint64_t val) {
  auto *var = f.ctx.CreateVariable(name, width);
  var->value = MakeLogic4VecVal(f.arena, width, val);
  var->is_signed = true;
  return var;
}
namespace {

// ==========================================================================
// Signed comparison — §11.4.4, §11.4.5, §11.8.1
// ==========================================================================
TEST(EvalAdv, SignedLtNeg) {
  EvalAdvFixture f;
  MakeSignedVarAdv(f, "sa", 8, 0xFF);
  MakeSignedVarAdv(f, "sb", 8, 0x01);
  auto *expr = MakeBinary(f.arena, TokenKind::kLt, MakeId(f.arena, "sa"),
                          MakeId(f.arena, "sb"));
  auto result = EvalExpr(expr, f.ctx, f.arena);
  EXPECT_EQ(result.ToUint64(), 1u);
}

TEST(EvalAdv, SignedGtNeg) {
  EvalAdvFixture f;
  MakeSignedVarAdv(f, "sa", 8, 0x01);
  MakeSignedVarAdv(f, "sb", 8, 0xFF);
  auto *expr = MakeBinary(f.arena, TokenKind::kGt, MakeId(f.arena, "sa"),
                          MakeId(f.arena, "sb"));
  auto result = EvalExpr(expr, f.ctx, f.arena);
  EXPECT_EQ(result.ToUint64(), 1u);
}

TEST(EvalAdv, UnsignedLtUnchanged) {
  EvalAdvFixture f;
  auto *a = MakeVar(f, "ua", 8, 0xFF);
  (void)a;
  auto *b = MakeVar(f, "ub", 8, 0x01);
  (void)b;
  auto *expr = MakeBinary(f.arena, TokenKind::kLt, MakeId(f.arena, "ua"),
                          MakeId(f.arena, "ub"));
  auto result = EvalExpr(expr, f.ctx, f.arena);
  EXPECT_EQ(result.ToUint64(), 0u);
}

} // namespace
