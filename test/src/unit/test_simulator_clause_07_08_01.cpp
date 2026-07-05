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

// §7.8.1 — driven through the full pipeline: an x/z index is also invalid when
// reading. A z-bearing index cannot match the stored key 5, so the read yields
// the array default (0) rather than the stored 77. Exercises the read path,
// distinct from the rejected write.
TEST(WildcardAssocArraySimulation, UnknownIndexReadReturnsDefaultEndToEnd) {
  auto v = RunAndGet(
      "module t;\n"
      "  int aa[*];\n"
      "  int result;\n"
      "  initial begin\n"
      "    aa[5] = 77;\n"
      "    result = aa[8'bz];\n"
      "  end\n"
      "endmodule\n",
      "result");
  EXPECT_EQ(v, 0u);
}

// §7.8.1 — driven through the full pipeline: an index carrying x/z is invalid
// at run time, so a write through it stores nothing. Observed with num(), which
// returns a count (permitted on a wildcard array, unlike an index-returning
// locator). The valid integral write on the same array is retained, isolating
// the x/z rejection from ordinary storage.
TEST(WildcardAssocArraySimulation, UnknownIndexNotStoredEndToEnd) {
  auto rejected = RunAndGet(
      "module t;\n"
      "  int aa[*];\n"
      "  int result;\n"
      "  initial begin\n"
      "    aa[8'bxx] = 9;\n"
      "    result = aa.num();\n"
      "  end\n"
      "endmodule\n",
      "result");
  EXPECT_EQ(rejected, 0u);

  auto stored = RunAndGet(
      "module t;\n"
      "  int aa[*];\n"
      "  int result;\n"
      "  initial begin\n"
      "    aa[3] = 9;\n"
      "    result = aa.num();\n"
      "  end\n"
      "endmodule\n",
      "result");
  EXPECT_EQ(stored, 1u);
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

// §7.8.1 — driven through the full pipeline: an index expression is
// self-determined and treated as unsigned. A signed 32-bit variable holding -1
// keys on its unsigned bit pattern (0xFFFFFFFF == 4294967295), so it addresses
// the same entry as the plain unsigned literal 32'hFFFFFFFF. Were the index
// sign-extended instead, the two writes/reads would land on different keys and
// the read would miss.
TEST(WildcardAssocArraySimulation, SignedVarIndexTreatedAsUnsignedEndToEnd) {
  auto v = RunAndGet(
      "module t;\n"
      "  int aa[*];\n"
      "  int s;\n"
      "  int result;\n"
      "  initial begin\n"
      "    s = -1;\n"
      "    aa[s] = 55;\n"
      "    result = aa[32'hFFFFFFFF];\n"
      "  end\n"
      "endmodule\n",
      "result");
  EXPECT_EQ(v, 55u);
}

}  // namespace
