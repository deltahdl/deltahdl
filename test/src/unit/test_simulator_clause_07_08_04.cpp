#include "fixture_simulator.h"
#include "parser/ast.h"
#include "simulator/evaluation.h"
#include "simulator/statement_assign.h"

using namespace delta;

static Expr* MakeAssocSelect(Arena& arena, std::string_view base_name,
                             int64_t idx_val) {
  auto* sel = arena.Create<Expr>();
  sel->kind = ExprKind::kSelect;
  auto* base = arena.Create<Expr>();
  base->kind = ExprKind::kIdentifier;
  base->text = base_name;
  sel->base = base;
  auto* idx = arena.Create<Expr>();
  idx->kind = ExprKind::kIntegerLiteral;
  idx->int_val = idx_val;
  sel->index = idx;
  return sel;
}

namespace {

// §7.8.4: Write and read with integral index.
TEST(IntegralIndexAssocArraySimulation, WriteAndRead) {
  SimFixture f;
  auto* aa = f.ctx.CreateAssocArray("aa", 32, false, 32);
  aa->int_data[5] = MakeLogic4VecVal(f.arena, 32, 42);

  EXPECT_EQ(aa->int_data[5].ToUint64(), 42u);
}

// §7.8.4: Multiple integral keys stored independently.
TEST(IntegralIndexAssocArraySimulation, MultipleKeys) {
  SimFixture f;
  auto* aa = f.ctx.CreateAssocArray("aa", 32, false, 32);
  aa->int_data[1] = MakeLogic4VecVal(f.arena, 32, 10);
  aa->int_data[2] = MakeLogic4VecVal(f.arena, 32, 20);
  aa->int_data[3] = MakeLogic4VecVal(f.arena, 32, 30);

  EXPECT_EQ(aa->Size(), 3u);
  EXPECT_EQ(aa->int_data[1].ToUint64(), 10u);
  EXPECT_EQ(aa->int_data[2].ToUint64(), 20u);
  EXPECT_EQ(aa->int_data[3].ToUint64(), 30u);
}

// §7.8.4: Overwriting an existing integral key.
TEST(IntegralIndexAssocArraySimulation, OverwriteKey) {
  SimFixture f;
  auto* aa = f.ctx.CreateAssocArray("aa", 32, false, 32);
  aa->int_data[7] = MakeLogic4VecVal(f.arena, 32, 100);
  aa->int_data[7] = MakeLogic4VecVal(f.arena, 32, 200);

  EXPECT_EQ(aa->int_data[7].ToUint64(), 200u);
}

// §7.8.4: Signed ordering — negative keys sort before positive.
TEST(IntegralIndexAssocArraySimulation, SignedOrdering) {
  SimFixture f;
  auto* aa = f.ctx.CreateAssocArray("aa", 32, false, 32);
  aa->int_data[10] = MakeLogic4VecVal(f.arena, 32, 1);
  aa->int_data[-5] = MakeLogic4VecVal(f.arena, 32, 2);
  aa->int_data[3] = MakeLogic4VecVal(f.arena, 32, 3);

  auto it = aa->int_data.begin();
  EXPECT_EQ(it->first, -5);
  ++it;
  EXPECT_EQ(it->first, 3);
  ++it;
  EXPECT_EQ(it->first, 10);
}

// §7.8.4: x/z index on write produces warning and skips write.
TEST(IntegralIndexAssocArraySimulation, XzIndexWriteWarns) {
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

// §7.8.4: x/z index on read produces warning.
TEST(IntegralIndexAssocArraySimulation, XzIndexReadWarns) {
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
  EvalExpr(sel, f.ctx, f.arena);
  EXPECT_GT(f.diag.WarningCount(), warns_before);
}

// §7.8.4: Negative keys work with signed int index.
TEST(IntegralIndexAssocArraySimulation, NegativeKeyAccess) {
  SimFixture f;
  f.ctx.CreateAssocArray("aa", 32, false, 32);

  auto* sel = MakeAssocSelect(f.arena, "aa", -3);
  auto* stmt = f.arena.Create<Stmt>();
  stmt->kind = StmtKind::kBlockingAssign;
  stmt->lhs = sel;
  stmt->rhs = f.arena.Create<Expr>();
  stmt->rhs->kind = ExprKind::kIntegerLiteral;
  stmt->rhs->int_val = 77;
  ExecBlockingAssignImpl(stmt, f.ctx, f.arena);

  auto* rd = MakeAssocSelect(f.arena, "aa", -3);
  auto result = EvalExpr(rd, f.ctx, f.arena);
  EXPECT_EQ(result.ToUint64(), 77u);
}

}  // namespace
