// §7.9: Associative array methods

#include <gtest/gtest.h>

#include <string>

#include "common/arena.h"
#include "common/diagnostic.h"
#include "common/source_mgr.h"
#include "lexer/lexer.h"
#include "parser/ast.h"
#include "parser/parser.h"
#include "simulation/eval.h"
#include "simulation/eval_array.h"
#include "simulation/sim_context.h"

using namespace delta;

// =============================================================================
// Helper fixture
// =============================================================================
struct AggFixture {
  SourceManager mgr;
  Arena arena;
  Scheduler scheduler{arena};
  DiagEngine diag{mgr};
  SimContext ctx{scheduler, arena, diag};
};

static Expr *MkAssocCall(Arena &arena, std::string_view var,
                         std::string_view method, std::string_view ref) {
  auto *expr = arena.Create<Expr>();
  expr->kind = ExprKind::kCall;
  auto *access = arena.Create<Expr>();
  access->kind = ExprKind::kMemberAccess;
  auto *base = arena.Create<Expr>();
  base->kind = ExprKind::kIdentifier;
  base->text = var;
  auto *meth = arena.Create<Expr>();
  meth->kind = ExprKind::kIdentifier;
  meth->text = method;
  access->lhs = base;
  access->rhs = meth;
  expr->lhs = access;
  auto *arg = arena.Create<Expr>();
  arg->kind = ExprKind::kIdentifier;
  arg->text = ref;
  expr->args.push_back(arg);
  return expr;
}
namespace {

TEST(AssocTraversal, FirstReturnsTruncationFlag) {
  AggFixture f;
  // 32-bit index type, ref variable is only 8 bits → truncation → returns -1.
  auto *aa = f.ctx.CreateAssocArray("aa", 32, false);
  aa->index_width = 32;
  aa->int_data[1000] = MakeLogic4VecVal(f.arena, 32, 42);
  auto *ref = f.ctx.CreateVariable("k", 8);
  ref->value = MakeLogic4VecVal(f.arena, 8, 0);
  Logic4Vec out{};
  auto *call = MkAssocCall(f.arena, "aa", "first", "k");
  bool ok = TryEvalAssocMethodCall(call, f.ctx, f.arena, out);
  ASSERT_TRUE(ok);
  // ref width (8) < index_width (32) → result should be -1 (as uint64 = max).
  // WriteTraversalKey returns -1, cast to uint64_t wraps.
  uint64_t r = out.ToUint64();
  // The result is stored as MakeLogic4VecVal(32, (uint64_t)-1) = 0xFFFFFFFF.
  EXPECT_EQ(r, static_cast<uint64_t>(static_cast<uint32_t>(-1)));
  // Key should still be written (truncated to 8 bits).
  EXPECT_EQ(ref->value.ToUint64(), 1000u & 0xFFu);
}

TEST(AssocTraversal, FirstReturnsOneWhenWidthSufficient) {
  AggFixture f;
  // 32-bit index, ref variable is also 32 bits → no truncation → returns 1.
  auto *aa = f.ctx.CreateAssocArray("aa", 32, false);
  aa->index_width = 32;
  aa->int_data[42] = MakeLogic4VecVal(f.arena, 32, 99);
  auto *ref = f.ctx.CreateVariable("k", 32);
  ref->value = MakeLogic4VecVal(f.arena, 32, 0);
  Logic4Vec out{};
  auto *call = MkAssocCall(f.arena, "aa", "first", "k");
  bool ok = TryEvalAssocMethodCall(call, f.ctx, f.arena, out);
  ASSERT_TRUE(ok);
  EXPECT_EQ(out.ToUint64(), 1u);
  EXPECT_EQ(ref->value.ToUint64(), 42u);
}

TEST(AssocTraversal, ByteIndexFirstReturnsOneForByteRef) {
  AggFixture f;
  // byte index type → index_width should be 8.
  auto *aa = f.ctx.CreateAssocArray("aa", 32, false);
  aa->index_width = 8;
  aa->int_data[200] = MakeLogic4VecVal(f.arena, 32, 99);
  auto *ref = f.ctx.CreateVariable("ix", 8);
  ref->value = MakeLogic4VecVal(f.arena, 8, 0);
  Logic4Vec out{};
  auto *call = MkAssocCall(f.arena, "aa", "first", "ix");
  bool ok = TryEvalAssocMethodCall(call, f.ctx, f.arena, out);
  ASSERT_TRUE(ok);
  // ref width (8) >= index_width (8) → returns 1 (no truncation).
  EXPECT_EQ(out.ToUint64(), 1u);
  EXPECT_EQ(ref->value.ToUint64(), 200u);
}

}  // namespace
