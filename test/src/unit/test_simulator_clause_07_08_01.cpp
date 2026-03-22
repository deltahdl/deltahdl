#include "fixture_simulator.h"
#include "helpers_scheduler.h"
#include "parser/ast.h"
#include "simulator/eval_array.h"
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

// §7.8.1: Write and read back an element with integral index.
TEST(WildcardAssocArraySimulation, WriteAndRead) {
  SimFixture f;
  f.ctx.CreateAssocArray("aa", 32, false);

  auto* sel = MakeAssocSelect(f.arena, "aa", 42);
  auto* stmt = f.arena.Create<Stmt>();
  stmt->kind = StmtKind::kBlockingAssign;
  stmt->lhs = sel;
  stmt->rhs = f.arena.Create<Expr>();
  stmt->rhs->kind = ExprKind::kIntegerLiteral;
  stmt->rhs->int_val = 100;
  ExecBlockingAssignImpl(stmt, f.ctx, f.arena);

  auto* rd = MakeAssocSelect(f.arena, "aa", 42);
  auto result = EvalExpr(rd, f.ctx, f.arena);
  EXPECT_EQ(result.ToUint64(), 100u);
}

// §7.8.1: Ordering is numerical — smallest to largest.
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

// §7.8.1: Multiple integral index values stored independently.
TEST(WildcardAssocArraySimulation, MultipleKeys) {
  SimFixture f;
  auto* aa = f.ctx.CreateAssocArray("aa", 32, false);
  aa->int_data[1] = MakeLogic4VecVal(f.arena, 32, 10);
  aa->int_data[2] = MakeLogic4VecVal(f.arena, 32, 20);
  aa->int_data[3] = MakeLogic4VecVal(f.arena, 32, 30);

  EXPECT_EQ(aa->Size(), 3u);
  EXPECT_EQ(aa->int_data[1].ToUint64(), 10u);
  EXPECT_EQ(aa->int_data[2].ToUint64(), 20u);
  EXPECT_EQ(aa->int_data[3].ToUint64(), 30u);
}

// §7.8.1: End-to-end write and read with wildcard array.
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

// §7.8.1: End-to-end multiple keys with wildcard array.
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

// §7.8.1: Overwriting a key replaces the previous value.
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

}  // namespace
