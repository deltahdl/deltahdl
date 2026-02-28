// §7.4: Packed and unpacked arrays

#include "fixture_simulator.h"
#include "helpers_array.h"
#include "parser/ast.h"
#include "simulator/eval.h"
#include "simulator/eval_array.h"

using namespace delta;

// =============================================================================
// Helper fixture
// =============================================================================
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

namespace {

TEST(ArraySlice, ReadSliceConcat) {
  SimFixture f;
  MakeArray4(f, "arr");
  // arr = {10, 20, 30, 40}.  arr[2:1] should give {arr[2], arr[1]} = {30, 20}.
  // Concatenated into a 16-bit value: arr[2] in high byte, arr[1] in low byte.
  auto result = EvalExpr(MkSlice(f.arena, "arr", 2, 1), f.ctx, f.arena);
  EXPECT_EQ(result.width, 16u);
  // arr[2]=30, arr[1]=20  →  (30 << 8) | 20 = 7700
  EXPECT_EQ(result.ToUint64(), (30u << 8) | 20u);
}

}  // namespace
