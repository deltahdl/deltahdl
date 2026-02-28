// §7.8.6: Accessing invalid indices


#include "parser/ast.h"
#include "simulator/eval.h"
#include "simulator/eval_array.h"

#include "fixture_simulator.h"

using namespace delta;

// =============================================================================
// Helper fixture
// =============================================================================
namespace {

// =============================================================================
// §7.8.6: Accessing invalid associative array indices
// =============================================================================
TEST(AssocArray, ReadMissingKeyWarns) {
  SimFixture f;
  auto* aa = f.ctx.CreateAssocArray("aa", 32, false);
  aa->int_data[10] = MakeLogic4VecVal(f.arena, 32, 42);
  // Read key 99 (does not exist).  Should return default and warn.
  auto* sel = f.arena.Create<Expr>();
  sel->kind = ExprKind::kSelect;
  auto* base = f.arena.Create<Expr>();
  base->kind = ExprKind::kIdentifier;
  base->text = "aa";
  sel->base = base;
  auto* idx = f.arena.Create<Expr>();
  idx->kind = ExprKind::kIntegerLiteral;
  idx->int_val = 99;
  sel->index = idx;
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
  auto* sel = f.arena.Create<Expr>();
  sel->kind = ExprKind::kSelect;
  auto* base = f.arena.Create<Expr>();
  base->kind = ExprKind::kIdentifier;
  base->text = "aa";
  sel->base = base;
  auto* idx = f.arena.Create<Expr>();
  idx->kind = ExprKind::kIntegerLiteral;
  idx->int_val = 10;
  sel->index = idx;
  uint32_t before = f.diag.WarningCount();
  auto result = EvalExpr(sel, f.ctx, f.arena);
  EXPECT_EQ(result.ToUint64(), 42u);
  EXPECT_EQ(f.diag.WarningCount(), before);
}

}  // namespace
