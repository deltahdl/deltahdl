// §7.4: Packed and unpacked arrays

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


static Expr* MkSlice(Arena& arena, std::string_view name, uint64_t hi,
                     uint64_t lo) {
  auto* sel = arena.Create<Expr>();
  sel->kind = ExprKind::kSelect;
  auto* base = arena.Create<Expr>();
  base->kind = ExprKind::kIdentifier;
  base->text = name;
  sel->base = base;
  auto* hi_expr = arena.Create<Expr>();
  hi_expr->kind = ExprKind::kIntegerLiteral;
  hi_expr->int_val = hi;
  sel->index = hi_expr;
  auto* lo_expr = arena.Create<Expr>();
  lo_expr->kind = ExprKind::kIntegerLiteral;
  lo_expr->int_val = lo;
  sel->index_end = lo_expr;
  return sel;
}

static void MakeArray4(AggFixture& f, std::string_view name) {
  f.ctx.RegisterArray(name, {0, 4, 8, false, false, false});
  for (uint32_t i = 0; i < 4; ++i) {
    auto tmp = std::string(name) + "[" + std::to_string(i) + "]";
    auto* s = f.arena.AllocString(tmp.c_str(), tmp.size());
    auto* v = f.ctx.CreateVariable(std::string_view(s, tmp.size()), 8);
    v->value = MakeLogic4VecVal(f.arena, 8, static_cast<uint64_t>(i + 1) * 10);
  }
}
namespace {

TEST(ArraySlice, ReadSliceConcat) {
  AggFixture f;
  MakeArray4(f, "arr");
  // arr = {10, 20, 30, 40}.  arr[2:1] should give {arr[2], arr[1]} = {30, 20}.
  // Concatenated into a 16-bit value: arr[2] in high byte, arr[1] in low byte.
  auto result = EvalExpr(MkSlice(f.arena, "arr", 2, 1), f.ctx, f.arena);
  EXPECT_EQ(result.width, 16u);
  // arr[2]=30, arr[1]=20  →  (30 << 8) | 20 = 7700
  EXPECT_EQ(result.ToUint64(), (30u << 8) | 20u);
}

}  // namespace
