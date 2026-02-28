// §7.8.6: Accessing invalid indices

#include "fixture_simulator.h"
#include "parser/ast.h"
#include "simulator/eval.h"
#include "simulator/eval_array.h"

using namespace delta;

// =============================================================================
// Helper fixture
// =============================================================================
static Expr* MakeAssocSelect(Arena& arena, int64_t idx_val) {
  auto* sel = arena.Create<Expr>();
  sel->kind = ExprKind::kSelect;
  auto* base = arena.Create<Expr>();
  base->kind = ExprKind::kIdentifier;
  base->text = "aa";
  sel->base = base;
  auto* idx = arena.Create<Expr>();
  idx->kind = ExprKind::kIntegerLiteral;
  idx->int_val = idx_val;
  sel->index = idx;
  return sel;
}

namespace {

// =============================================================================
// §7.8.6: Accessing invalid associative array indices
// =============================================================================
TEST(AssocArray, ReadMissingKeyWarns) {
  SimFixture f;
  auto* aa = f.ctx.CreateAssocArray("aa", 32, false);
  aa->int_data[10] = MakeLogic4VecVal(f.arena, 32, 42);
  // Read key 99 (does not exist).  Should return default and warn.
  auto* sel = MakeAssocSelect(f.arena, 99);
  uint32_t before = f.diag.WarningCount();
  auto result = EvalExpr(sel, f.ctx, f.arena);
  EXPECT_EQ(result.ToUint64(), 0u);
  EXPECT_GT(f.diag.WarningCount(), before);
}

TEST(AssocArray, ReadExistingKeyNoWarning) {
  SimFixture f;
  auto* aa = f.ctx.CreateAssocArray("aa", 32, false);
  aa->int_data[10] = MakeLogic4VecVal(f.arena, 32, 42);
  // Read key 10 (exists).  Should NOT warn.
  auto* sel = MakeAssocSelect(f.arena, 10);
  uint32_t before = f.diag.WarningCount();
  auto result = EvalExpr(sel, f.ctx, f.arena);
  EXPECT_EQ(result.ToUint64(), 42u);
  EXPECT_EQ(f.diag.WarningCount(), before);
}

}  // namespace
