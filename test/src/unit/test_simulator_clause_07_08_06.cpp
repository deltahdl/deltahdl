// §7.8.6: Accessing invalid indices

#include "common/arena.h"
#include "common/diagnostic.h"
#include "common/source_mgr.h"
#include "lexer/lexer.h"
#include "parser/ast.h"
#include "parser/parser.h"
#include "simulation/eval.h"
#include "simulation/eval_array.h"
#include "simulation/sim_context.h"
#include <gtest/gtest.h>
#include <string>

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

namespace {

// =============================================================================
// §7.8.6: Accessing invalid associative array indices
// =============================================================================
TEST(AssocArray, ReadMissingKeyWarns) {
  AggFixture f;
  auto *aa = f.ctx.CreateAssocArray("aa", 32, false);
  aa->int_data[10] = MakeLogic4VecVal(f.arena, 32, 42);
  // Read key 99 (does not exist).  Should return default and warn.
  auto *sel = f.arena.Create<Expr>();
  sel->kind = ExprKind::kSelect;
  auto *base = f.arena.Create<Expr>();
  base->kind = ExprKind::kIdentifier;
  base->text = "aa";
  sel->base = base;
  auto *idx = f.arena.Create<Expr>();
  idx->kind = ExprKind::kIntegerLiteral;
  idx->int_val = 99;
  sel->index = idx;
  uint32_t before = f.diag.WarningCount();
  auto result = EvalExpr(sel, f.ctx, f.arena);
  EXPECT_EQ(result.ToUint64(), 0u);
  EXPECT_GT(f.diag.WarningCount(), before);
}

TEST(AssocArray, ReadExistingKeyNoWarning) {
  AggFixture f;
  auto *aa = f.ctx.CreateAssocArray("aa", 32, false);
  aa->int_data[10] = MakeLogic4VecVal(f.arena, 32, 42);
  // Read key 10 (exists).  Should NOT warn.
  auto *sel = f.arena.Create<Expr>();
  sel->kind = ExprKind::kSelect;
  auto *base = f.arena.Create<Expr>();
  base->kind = ExprKind::kIdentifier;
  base->text = "aa";
  sel->base = base;
  auto *idx = f.arena.Create<Expr>();
  idx->kind = ExprKind::kIntegerLiteral;
  idx->int_val = 10;
  sel->index = idx;
  uint32_t before = f.diag.WarningCount();
  auto result = EvalExpr(sel, f.ctx, f.arena);
  EXPECT_EQ(result.ToUint64(), 42u);
  EXPECT_EQ(f.diag.WarningCount(), before);
}

} // namespace
