#include "fixture_simulator.h"
#include "parser/ast.h"
#include "simulator/eval_array.h"
#include "simulator/evaluation.h"
#include "simulator/statement_assign.h"

using namespace delta;

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

TEST(AssocArray, ReadMissingKeyWarns) {
  SimFixture f;
  auto* aa = f.ctx.CreateAssocArray("aa", 32, false);
  aa->int_data[10] = MakeLogic4VecVal(f.arena, 32, 42);

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

  auto* sel = MakeAssocSelect(f.arena, 10);
  uint32_t before = f.diag.WarningCount();
  auto result = EvalExpr(sel, f.ctx, f.arena);
  EXPECT_EQ(result.ToUint64(), 42u);
  EXPECT_EQ(f.diag.WarningCount(), before);
}

TEST(AssocArray, XzIndexWriteWarns) {
  SimFixture f;
  f.ctx.CreateAssocArray("aa", 32, false, 32);

  // Create a variable with x bits to use as index.
  auto* var = f.ctx.CreateLocalVariable("__xkey", 32);
  var->value = MakeLogic4VecVal(f.arena, 32, 5);
  var->value.words[0].bval = 0x1;

  auto* sel = f.arena.Create<Expr>();
  sel->kind = ExprKind::kSelect;
  auto* base = f.arena.Create<Expr>();
  base->kind = ExprKind::kIdentifier;
  base->text = "aa";
  sel->base = base;
  auto* xref = f.arena.Create<Expr>();
  xref->kind = ExprKind::kIdentifier;
  xref->text = "__xkey";
  sel->index = xref;

  auto rhs_val = MakeLogic4VecVal(f.arena, 32, 99);
  uint32_t warns_before = f.diag.WarningCount();
  TryAssocIndexedWrite(sel, rhs_val, f.ctx, f.arena);

  EXPECT_GT(f.diag.WarningCount(), warns_before);
  auto* aa = f.ctx.FindAssocArray("aa");
  EXPECT_EQ(aa->int_data.size(), 0u);
}

TEST(AssocArray, XzIndexReadWarns) {
  SimFixture f;
  auto* aa = f.ctx.CreateAssocArray("aa", 32, false, 32);
  aa->int_data[5] = MakeLogic4VecVal(f.arena, 32, 42);

  // Create a variable with x bits to use as index.
  auto* var = f.ctx.CreateLocalVariable("__xkey", 32);
  var->value = MakeLogic4VecVal(f.arena, 32, 5);
  var->value.words[0].bval = 0x1;

  auto* sel = f.arena.Create<Expr>();
  sel->kind = ExprKind::kSelect;
  auto* base = f.arena.Create<Expr>();
  base->kind = ExprKind::kIdentifier;
  base->text = "aa";
  sel->base = base;
  auto* xref = f.arena.Create<Expr>();
  xref->kind = ExprKind::kIdentifier;
  xref->text = "__xkey";
  sel->index = xref;

  uint32_t warns_before = f.diag.WarningCount();
  auto result = EvalExpr(sel, f.ctx, f.arena);
  EXPECT_GT(f.diag.WarningCount(), warns_before);
  EXPECT_EQ(result.ToUint64(), 0u);
}

TEST(AssocArray, ReadMissingKeyReturnsZeroFromEmptyArray) {
  SimFixture f;
  f.ctx.CreateAssocArray("aa", 32, false);

  auto* sel = MakeAssocSelect(f.arena, 0);
  uint32_t before = f.diag.WarningCount();
  auto result = EvalExpr(sel, f.ctx, f.arena);
  EXPECT_EQ(result.ToUint64(), 0u);
  EXPECT_GT(f.diag.WarningCount(), before);
}

TEST(AssocArray, ReadMissingKeyWithDefaultReturnsDefaultNoWarning) {
  SimFixture f;
  auto* aa = f.ctx.CreateAssocArray("aa", 32, false);
  aa->has_default = true;
  aa->default_value = MakeLogic4VecVal(f.arena, 32, 77);
  aa->int_data[1] = MakeLogic4VecVal(f.arena, 32, 10);

  auto* sel = MakeAssocSelect(f.arena, 99);
  uint32_t before = f.diag.WarningCount();
  auto result = EvalExpr(sel, f.ctx, f.arena);
  EXPECT_EQ(result.ToUint64(), 77u);
  EXPECT_EQ(f.diag.WarningCount(), before);
}

TEST(AssocArray, XzIndexReadWithDefaultReturnsDefaultValue) {
  SimFixture f;
  auto* aa = f.ctx.CreateAssocArray("aa", 32, false, 32);
  aa->has_default = true;
  aa->default_value = MakeLogic4VecVal(f.arena, 32, 55);
  aa->int_data[5] = MakeLogic4VecVal(f.arena, 32, 42);

  auto* var = f.ctx.CreateLocalVariable("__xkey", 32);
  var->value = MakeLogic4VecVal(f.arena, 32, 5);
  var->value.words[0].bval = 0x1;

  auto* sel = f.arena.Create<Expr>();
  sel->kind = ExprKind::kSelect;
  auto* base = f.arena.Create<Expr>();
  base->kind = ExprKind::kIdentifier;
  base->text = "aa";
  sel->base = base;
  auto* xref = f.arena.Create<Expr>();
  xref->kind = ExprKind::kIdentifier;
  xref->text = "__xkey";
  sel->index = xref;

  auto result = EvalExpr(sel, f.ctx, f.arena);
  EXPECT_EQ(result.ToUint64(), 55u);
}

TEST(AssocArray, ReadMissingStringKeyWarns) {
  SimFixture f;
  auto* aa = f.ctx.CreateAssocArray("bb", 32, true);
  aa->str_data["hello"] = MakeLogic4VecVal(f.arena, 32, 10);

  auto* sel = f.arena.Create<Expr>();
  sel->kind = ExprKind::kSelect;
  auto* base = f.arena.Create<Expr>();
  base->kind = ExprKind::kIdentifier;
  base->text = "bb";
  sel->base = base;
  auto* idx = f.arena.Create<Expr>();
  idx->kind = ExprKind::kStringLiteral;
  idx->text = "\"missing\"";
  sel->index = idx;

  uint32_t before = f.diag.WarningCount();
  auto result = EvalExpr(sel, f.ctx, f.arena);
  EXPECT_EQ(result.ToUint64(), 0u);
  EXPECT_GT(f.diag.WarningCount(), before);
}

TEST(AssocArray, XzIndexWriteDoesNotClobberExistingEntries) {
  SimFixture f;
  auto* aa = f.ctx.CreateAssocArray("aa", 32, false, 32);
  aa->int_data[5] = MakeLogic4VecVal(f.arena, 32, 42);

  auto* var = f.ctx.CreateLocalVariable("__xkey", 32);
  var->value = MakeLogic4VecVal(f.arena, 32, 5);
  var->value.words[0].bval = 0x1;

  auto* sel = f.arena.Create<Expr>();
  sel->kind = ExprKind::kSelect;
  auto* base = f.arena.Create<Expr>();
  base->kind = ExprKind::kIdentifier;
  base->text = "aa";
  sel->base = base;
  auto* xref = f.arena.Create<Expr>();
  xref->kind = ExprKind::kIdentifier;
  xref->text = "__xkey";
  sel->index = xref;

  auto rhs_val = MakeLogic4VecVal(f.arena, 32, 99);
  TryAssocIndexedWrite(sel, rhs_val, f.ctx, f.arena);

  EXPECT_EQ(aa->int_data.size(), 1u);
  EXPECT_EQ(aa->int_data[5].ToUint64(), 42u);
}

}  // namespace
