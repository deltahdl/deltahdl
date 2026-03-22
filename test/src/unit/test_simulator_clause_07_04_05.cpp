#include "builders_ast.h"
#include "fixture_simulator.h"
#include "helpers_array.h"
#include "helpers_scheduler.h"
#include "parser/ast.h"
#include "simulator/eval_array.h"
#include "simulator/evaluation.h"

using namespace delta;

static Expr* MkSlice(Arena& arena, std::string_view name, uint64_t hi,
                     uint64_t lo) {
  auto* sel = arena.Create<Expr>();
  sel->kind = ExprKind::kSelect;
  auto* base = arena.Create<Expr>();
  base->kind = ExprKind::kIdentifier;
  base->text = name;
  sel->base = base;
  auto* hi_expr = arena.Create<Expr>();
  hi_expr->kind = ExprKind::kIntegerLiteral;
  hi_expr->int_val = hi;
  sel->index = hi_expr;
  auto* lo_expr = arena.Create<Expr>();
  lo_expr->kind = ExprKind::kIntegerLiteral;
  lo_expr->int_val = lo;
  sel->index_end = lo_expr;
  return sel;
}

namespace {

TEST(ArrayIndexingAndSlicing, OutOfBoundsReturnsX) {
  SimFixture f;

  f.ctx.RegisterArray("arr", {0, 4, 8, false, false, false});
  for (uint32_t i = 0; i < 4; ++i) {
    auto tmp = "arr[" + std::to_string(i) + "]";
    auto* s = f.arena.AllocString(tmp.c_str(), tmp.size());
    auto* v = f.ctx.CreateVariable(std::string_view(s, tmp.size()), 8);
    v->value = MakeLogic4VecVal(f.arena, 8, static_cast<uint64_t>(i + 1) * 10);
  }

  auto in_result = EvalExpr(MakeSelect(f.arena, "arr", 2), f.ctx, f.arena);
  EXPECT_EQ(in_result.ToUint64(), 30u);
  EXPECT_TRUE(in_result.IsKnown());

  auto oob_result = EvalExpr(MakeSelect(f.arena, "arr", 10), f.ctx, f.arena);
  EXPECT_FALSE(oob_result.IsKnown());
}

TEST(ArrayIndexingAndSlicing, ReadSliceConcat) {
  SimFixture f;
  MakeArray4(f, "arr");

  auto result = EvalExpr(MkSlice(f.arena, "arr", 2, 1), f.ctx, f.arena);
  EXPECT_EQ(result.width, 16u);

  EXPECT_EQ(result.ToUint64(), (30u << 8) | 20u);
}

// §7.4.5: Write to out-of-bounds index performs no operation.
TEST(ArrayIndexingAndSlicing, WriteOutOfBoundsIsNoop) {
  SimFixture f;

  f.ctx.RegisterArray("arr", {0, 4, 8, false, false, false});
  for (uint32_t i = 0; i < 4; ++i) {
    auto tmp = "arr[" + std::to_string(i) + "]";
    auto* s = f.arena.AllocString(tmp.c_str(), tmp.size());
    auto* v = f.ctx.CreateVariable(std::string_view(s, tmp.size()), 8);
    v->value = MakeLogic4VecVal(f.arena, 8, static_cast<uint64_t>(i + 1) * 10);
  }

  auto before = EvalExpr(MakeSelect(f.arena, "arr", 1), f.ctx, f.arena);
  EXPECT_EQ(before.ToUint64(), 20u);

  // Out-of-bounds element does not exist — no variable created.
  auto* oob = f.ctx.FindVariable("arr[10]");
  EXPECT_EQ(oob, nullptr);

  // Original element unchanged.
  auto after = EvalExpr(MakeSelect(f.arena, "arr", 1), f.ctx, f.arena);
  EXPECT_EQ(after.ToUint64(), 20u);
}

// §7.4.5: Part-select on packed array.
TEST(ArrayIndexingAndSlicing, PartSelectOnPackedArray) {
  auto v = RunAndGet(
      "module t;\n"
      "  logic [63:0] data;\n"
      "  logic [7:0] result;\n"
      "  initial begin\n"
      "    data = 64'hDEADBEEF_CAFEBABE;\n"
      "    result = data[23:16];\n"
      "  end\n"
      "endmodule\n",
      "result");
  EXPECT_EQ(v, 0xBEu);
}

// §7.4.5: Indexed part-select ascending (+:).
TEST(ArrayIndexingAndSlicing, IndexedPartSelectPlus) {
  auto v = RunAndGet(
      "module t;\n"
      "  logic [31:0] vec;\n"
      "  logic [7:0] result;\n"
      "  int base;\n"
      "  initial begin\n"
      "    vec = 32'hAABBCCDD;\n"
      "    base = 8;\n"
      "    result = vec[base +: 8];\n"
      "  end\n"
      "endmodule\n",
      "result");
  EXPECT_EQ(v, 0xCCu);
}

// §7.4.5: Indexed part-select descending (-:).
TEST(ArrayIndexingAndSlicing, IndexedPartSelectMinus) {
  auto v = RunAndGet(
      "module t;\n"
      "  logic [31:0] vec;\n"
      "  logic [7:0] result;\n"
      "  int base;\n"
      "  initial begin\n"
      "    vec = 32'hAABBCCDD;\n"
      "    base = 15;\n"
      "    result = vec[base -: 8];\n"
      "  end\n"
      "endmodule\n",
      "result");
  EXPECT_EQ(v, 0xCCu);
}

}  // namespace
