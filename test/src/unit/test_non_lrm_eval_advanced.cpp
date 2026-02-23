// Non-LRM tests

#include <gtest/gtest.h>

#include <cstring>

#include "common/arena.h"
#include "common/diagnostic.h"
#include "common/source_mgr.h"
#include "lexer/token.h"
#include "parser/ast.h"
#include "simulation/adv_sim.h"
#include "simulation/eval.h"
#include "simulation/sim_context.h"  // StructTypeInfo, StructFieldInfo

using namespace delta;

// Shared fixture for advanced expression evaluation tests (§11 phases 22+).
struct EvalAdvFixture {
  SourceManager mgr;
  Arena arena;
  Scheduler scheduler{arena};
  DiagEngine diag{mgr};
  SimContext ctx{scheduler, arena, diag};
};

static Expr *MakeInt(Arena &arena, uint64_t val) {
  auto *e = arena.Create<Expr>();
  e->kind = ExprKind::kIntegerLiteral;
  e->int_val = val;
  return e;
}

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

static Expr *MakeRange(Arena &arena, Expr *lo, Expr *hi,
                       TokenKind op = TokenKind::kEof) {
  auto *r = arena.Create<Expr>();
  r->kind = ExprKind::kSelect;
  r->index = lo;
  r->index_end = hi;
  r->op = op;
  return r;
}
namespace {

// ==========================================================================
// §11.3.6: Assignment within expression
// ==========================================================================
TEST(EvalAdv, AssignInExprBasic) {
  EvalAdvFixture f;
  // (a = 42) should assign 42 to a and return 42.
  MakeVar(f, "aie", 32, 0);
  auto *assign = f.arena.Create<Expr>();
  assign->kind = ExprKind::kBinary;
  assign->op = TokenKind::kEq;
  assign->lhs = MakeId(f.arena, "aie");
  assign->rhs = MakeInt(f.arena, 42);
  auto result = EvalExpr(assign, f.ctx, f.arena);
  EXPECT_EQ(result.ToUint64(), 42u);
  auto *var = f.ctx.FindVariable("aie");
  EXPECT_EQ(var->value.ToUint64(), 42u);
}

TEST(EvalAdv, AssignInExprTruncToLHSWidth) {
  EvalAdvFixture f;
  // (b = 0x1FF) where b is 8-bit should truncate to 0xFF.
  MakeVar(f, "aie8", 8, 0);
  auto *assign = f.arena.Create<Expr>();
  assign->kind = ExprKind::kBinary;
  assign->op = TokenKind::kEq;
  assign->lhs = MakeId(f.arena, "aie8");
  assign->rhs = MakeInt(f.arena, 0x1FF);
  auto result = EvalExpr(assign, f.ctx, f.arena);
  // §11.3.6: Result should be cast to LHS type (8-bit).
  EXPECT_EQ(result.width, 8u);
  EXPECT_EQ(result.ToUint64(), 0xFFu);
}

TEST(EvalAdv, InsideAbsTolerance) {
  EvalAdvFixture f;
  auto *var = f.ctx.CreateVariable("at", 8);
  var->value = MakeLogic4VecVal(f.arena, 8, 10);
  auto *inside = f.arena.Create<Expr>();
  inside->kind = ExprKind::kInside;
  inside->lhs = MakeId(f.arena, "at");
  inside->elements.push_back(MakeRange(f.arena, MakeInt(f.arena, 7),
                                       MakeInt(f.arena, 5),
                                       TokenKind::kPlusSlashMinus));
  auto result = EvalExpr(inside, f.ctx, f.arena);
  EXPECT_EQ(result.ToUint64(), 1u);
}

TEST(EvalAdv, InsideAbsToleranceMiss) {
  EvalAdvFixture f;
  auto *var = f.ctx.CreateVariable("am", 8);
  var->value = MakeLogic4VecVal(f.arena, 8, 20);
  auto *inside = f.arena.Create<Expr>();
  inside->kind = ExprKind::kInside;
  inside->lhs = MakeId(f.arena, "am");
  inside->elements.push_back(MakeRange(f.arena, MakeInt(f.arena, 7),
                                       MakeInt(f.arena, 5),
                                       TokenKind::kPlusSlashMinus));
  auto result = EvalExpr(inside, f.ctx, f.arena);
  EXPECT_EQ(result.ToUint64(), 0u);
}

TEST(EvalAdv, InsideRelTolerance) {
  EvalAdvFixture f;
  auto *var = f.ctx.CreateVariable("rt", 8);
  var->value = MakeLogic4VecVal(f.arena, 8, 8);
  auto *inside = f.arena.Create<Expr>();
  inside->kind = ExprKind::kInside;
  inside->lhs = MakeId(f.arena, "rt");
  inside->elements.push_back(MakeRange(f.arena, MakeInt(f.arena, 10),
                                       MakeInt(f.arena, 25),
                                       TokenKind::kPlusPercentMinus));
  auto result = EvalExpr(inside, f.ctx, f.arena);
  EXPECT_EQ(result.ToUint64(), 1u);
}

// =============================================================================
// TwoStateDetector
// =============================================================================
TEST(AdvSim, TwoStateDetectorKnown2State) {
  Arena arena;
  auto vec = MakeLogic4VecVal(arena, 8, 0x42);
  EXPECT_TRUE(TwoStateDetector::Is2State(vec));
}

TEST(AdvSim, TwoStateDetectorWith4StateValue) {
  Arena arena;
  auto vec = MakeLogic4Vec(arena, 8);
  // Set bval to non-zero to indicate X/Z.
  vec.words[0].bval = 0x01;
  EXPECT_FALSE(TwoStateDetector::Is2State(vec));
}

TEST(AdvSim, TwoStateDetectorZeroWidth) {
  Logic4Vec empty;
  empty.width = 0;
  empty.nwords = 0;
  empty.words = nullptr;
  EXPECT_TRUE(TwoStateDetector::Is2State(empty));
}

}  // namespace
