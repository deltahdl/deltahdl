#include <gtest/gtest.h>

#include <cstdint>
#include <string>

#include "common/types.h"
#include "fixture_simulator.h"
#include "helpers_assoc.h"
#include "helpers_assoc_multikey.h"
#include "helpers_reported_error.h"
#include "helpers_scheduler.h"
#include "parser/ast_expr.h"
#include "parser/ast_stmt.h"
#include "simulator/eval_array.h"
#include "simulator/evaluation.h"
#include "simulator/lowerer.h"
#include "simulator/sim_context_types.h"
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

TEST(WildcardAssocArraySimulation, UnsignedKeyOrdering) {
  SimFixture f;
  auto* aa = f.ctx.CreateAssocArray("aa", 32, false, AssocArraySpec{32, true});

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

TEST(WildcardAssocArraySimulation, ForeachRejectionNames7_8_1) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "module t;\n"
      "  int aa[*];\n"
      "  int result;\n"
      "  initial begin\n"
      "    aa[3] = 9;\n"
      "    foreach (aa[i]) result = aa[i];\n"
      "  end\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  Lowerer lowerer(f.ctx, f.arena, f.diag);
  lowerer.Lower(design);
  f.scheduler.Run();
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "foreach not allowed on wildcard associative array",
                            6, "7.8.1"));
}

TEST(WildcardAssocArraySimulation, IndexIsKeyedByItsWholeValue) {
  SimFixture f;
  std::string out = RunCapture(
      "module t;\n"
      "  int c [*];\n"
      "  initial begin\n"
      "    c[100'h1_0000_0000_0000_0000] = 1;\n"
      "    c[100'h2_0000_0000_0000_0000] = 2;\n"
      "    c[3'b101] = 3;\n"
      "    c[8'd5] = 4;\n"
      "    $display(\"%0d %0d %0d %0d\", c.num(), "
      "c[100'h1_0000_0000_0000_0000],\n"
      "             c[100'h2_0000_0000_0000_0000], c[5]);\n"
      "  end\n"
      "endmodule\n",
      f);
  EXPECT_EQ(out, "3 1 2 4\n");
}

}  // namespace
