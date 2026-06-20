#include "fixture_simulator.h"
#include "helpers_assoc.h"
#include "helpers_assoc_multikey.h"
#include "helpers_scheduler.h"
#include "parser/ast.h"
#include "simulator/eval_array.h"
#include "simulator/evaluation.h"
#include "simulator/statement_assign.h"

using namespace delta;

namespace {

TEST(WildcardAssocArraySimulation, WriteAndRead) {
  SimFixture f;
  f.ctx.CreateAssocArray("aa", 32, false);

  auto* sel = MakeAssocSelect(f.arena, 42);
  auto* stmt = f.arena.Create<Stmt>();
  stmt->kind = StmtKind::kBlockingAssign;
  stmt->lhs = sel;
  stmt->rhs = f.arena.Create<Expr>();
  stmt->rhs->kind = ExprKind::kIntegerLiteral;
  stmt->rhs->int_val = 100;
  ExecBlockingAssignImpl(stmt, f.ctx, f.arena);

  auto* rd = MakeAssocSelect(f.arena, 42);
  auto result = EvalExpr(rd, f.ctx, f.arena);
  EXPECT_EQ(result.ToUint64(), 100u);
}

TEST(WildcardAssocArraySimulation, NumericalOrdering) {
  SimFixture f;
  auto* aa = f.ctx.CreateAssocArray("aa", 32, false);
  aa->int_data[30] = MakeLogic4VecVal(f.arena, 32, 300);
  aa->int_data[10] = MakeLogic4VecVal(f.arena, 32, 100);
  aa->int_data[20] = MakeLogic4VecVal(f.arena, 32, 200);

  auto it = aa->int_data.begin();
  EXPECT_EQ(it->first, 10);
  ++it;
  EXPECT_EQ(it->first, 20);
  ++it;
  EXPECT_EQ(it->first, 30);
}

TEST(WildcardAssocArraySimulation, MultipleKeys) {
  SimFixture f;
  auto* aa = f.ctx.CreateAssocArray("aa", 32, false);
  FillAndCheckThreeKeys(f, aa);
}

TEST(WildcardAssocArraySimulation, EndToEndWriteRead) {
  auto v = RunAndGet(
      "module t;\n"
      "  int aa[*];\n"
      "  int result;\n"
      "  initial begin\n"
      "    aa[5] = 77;\n"
      "    result = aa[5];\n"
      "  end\n"
      "endmodule\n",
      "result");
  EXPECT_EQ(v, 77u);
}

TEST(WildcardAssocArraySimulation, EndToEndMultipleKeys) {
  auto v = RunAndGet(
      "module t;\n"
      "  int aa[*];\n"
      "  int result;\n"
      "  initial begin\n"
      "    aa[1] = 10;\n"
      "    aa[2] = 20;\n"
      "    aa[3] = 30;\n"
      "    result = aa[2];\n"
      "  end\n"
      "endmodule\n",
      "result");
  EXPECT_EQ(v, 20u);
}

TEST(WildcardAssocArraySimulation, OverwriteKey) {
  auto v = RunAndGet(
      "module t;\n"
      "  int aa[*];\n"
      "  int result;\n"
      "  initial begin\n"
      "    aa[7] = 100;\n"
      "    aa[7] = 999;\n"
      "    result = aa[7];\n"
      "  end\n"
      "endmodule\n",
      "result");
  EXPECT_EQ(v, 999u);
}

// §7.8.1 — wildcard indexing expressions are self-determined and treated as
// unsigned: a value with its high bit set must key on its unsigned magnitude,
// not a sign-extended negative.
TEST(WildcardAssocArraySimulation, IndexTreatedAsUnsigned) {
  SimFixture f;
  auto* aa = f.ctx.CreateAssocArray(
      "aa", 32, /*is_string_key=*/false,
      AssocArraySpec{/*index_width=*/32, /*is_wildcard=*/true});

  auto* sel = MakeAssocSelect(f.arena, 0xFFFFFFFF);
  auto* stmt = f.arena.Create<Stmt>();
  stmt->kind = StmtKind::kBlockingAssign;
  stmt->lhs = sel;
  stmt->rhs = f.arena.Create<Expr>();
  stmt->rhs->kind = ExprKind::kIntegerLiteral;
  stmt->rhs->int_val = 5;
  ExecBlockingAssignImpl(stmt, f.ctx, f.arena);

  EXPECT_EQ(aa->int_data.count(4294967295), 1u);
  EXPECT_EQ(aa->int_data.count(-1), 0u);
}

// §7.8.1 — the same numeric value carried by indices of differing widths
// collapses to a single entry (leading zeros dropped, minimal value used).
TEST(WildcardAssocArraySimulation, EquivalentWidthsCollapse) {
  auto v = RunAndGet(
      "module t;\n"
      "  int aa[*];\n"
      "  int result;\n"
      "  initial begin\n"
      "    aa[8'd5] = 77;\n"
      "    result = aa[32'd5];\n"
      "  end\n"
      "endmodule\n",
      "result");
  EXPECT_EQ(v, 77u);
}

// §7.8.1 — a 4-state index value containing x or z is invalid, so the write is
// rejected and no entry is created.
TEST(WildcardAssocArraySimulation, UnknownIndexNotStored) {
  SimFixture f;
  auto* aa = f.ctx.CreateAssocArray(
      "aa", 32, /*is_string_key=*/false,
      AssocArraySpec{/*index_width=*/32, /*is_wildcard=*/true});

  auto* sel = f.arena.Create<Expr>();
  sel->kind = ExprKind::kSelect;
  auto* base = f.arena.Create<Expr>();
  base->kind = ExprKind::kIdentifier;
  base->text = "aa";
  sel->base = base;
  auto* idx = f.arena.Create<Expr>();
  idx->kind = ExprKind::kIntegerLiteral;
  idx->text = "8'bx";
  sel->index = idx;

  auto* stmt = f.arena.Create<Stmt>();
  stmt->kind = StmtKind::kBlockingAssign;
  stmt->lhs = sel;
  stmt->rhs = f.arena.Create<Expr>();
  stmt->rhs->kind = ExprKind::kIntegerLiteral;
  stmt->rhs->int_val = 9;
  ExecBlockingAssignImpl(stmt, f.ctx, f.arena);

  EXPECT_EQ(aa->Size(), 0u);
}

// §7.8.1 — a string literal index is cast to a bit vector of equivalent size,
// so "AB" (16 bits) keys identically to its numeric value 0x4142.
TEST(WildcardAssocArraySimulation, StringLiteralIndexCastToVector) {
  auto v = RunAndGet(
      "module t;\n"
      "  int aa[*];\n"
      "  int result;\n"
      "  initial begin\n"
      "    aa[\"AB\"] = 7;\n"
      "    result = aa[16'h4142];\n"
      "  end\n"
      "endmodule\n",
      "result");
  EXPECT_EQ(v, 7u);
}

// §7.8.1 — the equivalent-size cast tracks the literal's length: a one-byte
// string "A" becomes an 8-bit value 0x41, keying the same entry as 8'h41.
TEST(WildcardAssocArraySimulation, SingleCharStringLiteralIndex) {
  auto v = RunAndGet(
      "module t;\n"
      "  int aa[*];\n"
      "  int result;\n"
      "  initial begin\n"
      "    aa[\"A\"] = 9;\n"
      "    result = aa[8'h41];\n"
      "  end\n"
      "endmodule\n",
      "result");
  EXPECT_EQ(v, 9u);
}

// §7.8.1 — an x/z index is also invalid when reading: it cannot match any
// stored entry, so the read yields the array default rather than a stored
// value. Exercises the read path (distinct from the rejected write).
TEST(WildcardAssocArraySimulation, UnknownIndexReadReturnsDefault) {
  SimFixture f;
  auto* aa = f.ctx.CreateAssocArray(
      "aa", 32, /*is_string_key=*/false,
      AssocArraySpec{/*index_width=*/32, /*is_wildcard=*/true});
  aa->int_data[5] = MakeLogic4VecVal(f.arena, 32, 77);

  auto* rd = f.arena.Create<Expr>();
  rd->kind = ExprKind::kSelect;
  auto* base = f.arena.Create<Expr>();
  base->kind = ExprKind::kIdentifier;
  base->text = "aa";
  rd->base = base;
  auto* idx = f.arena.Create<Expr>();
  idx->kind = ExprKind::kIntegerLiteral;
  idx->text = "8'bz";
  rd->index = idx;

  auto result = EvalExpr(rd, f.ctx, f.arena);
  EXPECT_EQ(result.ToUint64(), 0u);
}

// §7.8.1 — because indices are treated as unsigned, a key with its top bit set
// is the largest value and orders after a small key, rather than sorting first
// as it would under a signed interpretation.
TEST(WildcardAssocArraySimulation, UnsignedKeyOrdering) {
  SimFixture f;
  auto* aa = f.ctx.CreateAssocArray(
      "aa", 32, /*is_string_key=*/false,
      AssocArraySpec{/*index_width=*/32, /*is_wildcard=*/true});

  for (int64_t k : {int64_t{1}, int64_t{0xFFFFFFFF}}) {
    auto* sel = MakeAssocSelect(f.arena, k);
    auto* stmt = f.arena.Create<Stmt>();
    stmt->kind = StmtKind::kBlockingAssign;
    stmt->lhs = sel;
    stmt->rhs = f.arena.Create<Expr>();
    stmt->rhs->kind = ExprKind::kIntegerLiteral;
    stmt->rhs->int_val = k;
    ExecBlockingAssignImpl(stmt, f.ctx, f.arena);
  }

  ASSERT_EQ(aa->int_data.size(), 2u);
  auto it = aa->int_data.begin();
  EXPECT_EQ(it->first, 1);
  ++it;
  EXPECT_EQ(it->first, 4294967295);
}

}  // namespace
