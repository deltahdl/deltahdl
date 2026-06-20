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

TEST(IntegralIndexAssocArraySimulation, WriteAndRead) {
  SimFixture f;
  auto* aa = f.ctx.CreateAssocArray("aa", 32, false, 32);
  aa->int_data[5] = MakeLogic4VecVal(f.arena, 32, 42);

  EXPECT_EQ(aa->int_data[5].ToUint64(), 42u);
}

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

TEST(IntegralIndexAssocArraySimulation, OverwriteKey) {
  SimFixture f;
  auto* aa = f.ctx.CreateAssocArray("aa", 32, false, 32);
  aa->int_data[7] = MakeLogic4VecVal(f.arena, 32, 100);
  aa->int_data[7] = MakeLogic4VecVal(f.arena, 32, 200);

  EXPECT_EQ(aa->int_data[7].ToUint64(), 200u);
}

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

static void WriteAssoc(SimFixture& f, std::string_view name, int64_t idx,
                       int64_t val) {
  auto* stmt = f.arena.Create<Stmt>();
  stmt->kind = StmtKind::kBlockingAssign;
  stmt->lhs = MakeAssocSelect(f.arena, name, idx);
  stmt->rhs = f.arena.Create<Expr>();
  stmt->rhs->kind = ExprKind::kIntegerLiteral;
  stmt->rhs->int_val = val;
  ExecBlockingAssignImpl(stmt, f.ctx, f.arena);
}

// §7.8.4: the index expression is cast to the index type. For an unsigned
// 8-bit index type, the value 200 stays 200 (zero-extended), so it must not
// alias the sign-extended key -56.
TEST(IntegralIndexAssocArraySimulation, UnsignedIndexZeroExtension) {
  SimFixture f;
  auto* aa = f.ctx.CreateAssocArray("aa", 32, false, /*index_width=*/8,
                                    /*is_wildcard=*/false, /*is_4state=*/false,
                                    /*is_index_signed=*/false);
  WriteAssoc(f, "aa", 200, 77);

  EXPECT_EQ(aa->int_data.count(200), 1u);
  EXPECT_EQ(aa->int_data.count(-56), 0u);
}

// §7.8.4: casting to the index type narrows a value wider than the index
// width, so 456 (0x1C8) collapses onto the 8-bit key 200 (0xC8).
TEST(IntegralIndexAssocArraySimulation, IndexTruncatedToWidth) {
  SimFixture f;
  auto* aa = f.ctx.CreateAssocArray("aa", 32, false, /*index_width=*/8,
                                    /*is_wildcard=*/false, /*is_4state=*/false,
                                    /*is_index_signed=*/false);
  WriteAssoc(f, "aa", 456, 77);

  EXPECT_EQ(aa->int_data.count(200), 1u);
  EXPECT_EQ(aa->int_data.count(456), 0u);
  EXPECT_EQ(aa->Size(), 1u);
}

// §7.8.4: a signed 8-bit index type sign-extends, so 200 becomes the key -56.
TEST(IntegralIndexAssocArraySimulation, SignedIndexSignExtension) {
  SimFixture f;
  auto* aa = f.ctx.CreateAssocArray("aa", 32, false, /*index_width=*/8,
                                    /*is_wildcard=*/false, /*is_4state=*/false,
                                    /*is_index_signed=*/true);
  WriteAssoc(f, "aa", 200, 77);

  EXPECT_EQ(aa->int_data.count(-56), 1u);
  EXPECT_EQ(aa->int_data.count(200), 0u);
}

// §7.8.4: an unsigned index type orders entries by unsigned numerical value,
// so 200 follows 10 rather than preceding it as a sign-extended key would.
TEST(IntegralIndexAssocArraySimulation, UnsignedOrdering) {
  SimFixture f;
  auto* aa = f.ctx.CreateAssocArray("aa", 32, false, /*index_width=*/8,
                                    /*is_wildcard=*/false, /*is_4state=*/false,
                                    /*is_index_signed=*/false);
  WriteAssoc(f, "aa", 200, 1);
  WriteAssoc(f, "aa", 10, 2);

  auto it = aa->int_data.begin();
  EXPECT_EQ(it->first, 10);
  ++it;
  EXPECT_EQ(it->first, 200);
}

// §7.8.4: a 4-state index expression containing x or z is invalid; the write
// is flagged with a diagnostic rather than allocating an entry.
TEST(IntegralIndexAssocArraySimulation, XZIndexInvalid) {
  SimFixture f;
  auto* aa = f.ctx.CreateAssocArray("aa", 32, false, /*index_width=*/8,
                                    /*is_wildcard=*/false, /*is_4state=*/true);
  auto* ix = f.ctx.CreateVariable("ix", 8);
  ix->value = MakeAllX(f.arena, 8);

  auto* sel = f.arena.Create<Expr>();
  sel->kind = ExprKind::kSelect;
  auto* base = f.arena.Create<Expr>();
  base->kind = ExprKind::kIdentifier;
  base->text = "aa";
  sel->base = base;
  auto* idx = f.arena.Create<Expr>();
  idx->kind = ExprKind::kIdentifier;
  idx->text = "ix";
  sel->index = idx;

  auto* stmt = f.arena.Create<Stmt>();
  stmt->kind = StmtKind::kBlockingAssign;
  stmt->lhs = sel;
  stmt->rhs = f.arena.Create<Expr>();
  stmt->rhs->kind = ExprKind::kIntegerLiteral;
  stmt->rhs->int_val = 77;
  ExecBlockingAssignImpl(stmt, f.ctx, f.arena);

  EXPECT_GE(f.diag.WarningCount(), 1u);
  EXPECT_TRUE(aa->int_data.empty());
}

// §7.8.4: the index cast applies on reads as well as writes. An entry stored
// under an unsigned 8-bit index of 200 is found again by reading 200, which
// confirms the read path zero-extends to the same key instead of sign-extending
// to -56.
TEST(IntegralIndexAssocArraySimulation, UnsignedCastReadRoundtrip) {
  SimFixture f;
  f.ctx.CreateAssocArray("aa", 32, false, /*index_width=*/8,
                         /*is_wildcard=*/false, /*is_4state=*/false,
                         /*is_index_signed=*/false);
  WriteAssoc(f, "aa", 200, 99);

  auto* rd = MakeAssocSelect(f.arena, "aa", 200);
  auto result = EvalExpr(rd, f.ctx, f.arena);
  EXPECT_EQ(result.ToUint64(), 99u);
}

// §7.8.4: a 4-state index containing x or z is invalid on reads too, so the
// read is flagged with a diagnostic rather than treated as a valid lookup.
TEST(IntegralIndexAssocArraySimulation, XZIndexInvalidOnRead) {
  SimFixture f;
  f.ctx.CreateAssocArray("aa", 32, false, /*index_width=*/8,
                         /*is_wildcard=*/false, /*is_4state=*/true);
  auto* ix = f.ctx.CreateVariable("ix", 8);
  ix->value = MakeAllX(f.arena, 8);

  auto* sel = f.arena.Create<Expr>();
  sel->kind = ExprKind::kSelect;
  auto* base = f.arena.Create<Expr>();
  base->kind = ExprKind::kIdentifier;
  base->text = "aa";
  sel->base = base;
  auto* idx = f.arena.Create<Expr>();
  idx->kind = ExprKind::kIdentifier;
  idx->text = "ix";
  sel->index = idx;

  EvalExpr(sel, f.ctx, f.arena);
  EXPECT_GE(f.diag.WarningCount(), 1u);
}

}  // namespace
