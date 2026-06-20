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

static Expr* MkPlusPartSelect(Arena& arena, std::string_view name,
                              std::string_view pos_var, uint64_t size) {
  auto* sel = arena.Create<Expr>();
  sel->kind = ExprKind::kSelect;
  sel->is_part_select_plus = true;
  auto* base = arena.Create<Expr>();
  base->kind = ExprKind::kIdentifier;
  base->text = name;
  sel->base = base;
  auto* pos = arena.Create<Expr>();
  pos->kind = ExprKind::kIdentifier;
  pos->text = pos_var;
  sel->index = pos;
  auto* width = arena.Create<Expr>();
  width->kind = ExprKind::kIntegerLiteral;
  width->int_val = size;
  sel->index_end = width;
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

TEST(ArrayIndexingAndSlicing, TwoStateInvalidIndexReadsZero) {
  // Table 7-1: an invalid index read of an unpacked array of a 2-state
  // integral type yields '0 (a known value), in contrast to the 'x produced
  // for a 4-state element type.
  SimFixture f;

  f.ctx.RegisterArray("barr",
                      {0, 4, 8, false, false, false, /*is_4state=*/false});
  for (uint32_t i = 0; i < 4; ++i) {
    auto tmp = "barr[" + std::to_string(i) + "]";
    auto* s = f.arena.AllocString(tmp.c_str(), tmp.size());
    auto* v = f.ctx.CreateVariable(std::string_view(s, tmp.size()), 8);
    v->value = MakeLogic4VecVal(f.arena, 8, static_cast<uint64_t>(i + 1) * 10);
  }

  auto oob = EvalExpr(MakeSelect(f.arena, "barr", 10), f.ctx, f.arena);
  EXPECT_TRUE(oob.IsKnown());
  EXPECT_EQ(oob.ToUint64(), 0u);
}

TEST(ArrayIndexingAndSlicing, UnknownIndexBitMakesIndexInvalid) {
  // An index expression with any x or z bit makes the index invalid, just as
  // an out-of-bounds index does; the read of the 4-state array then returns x.
  SimFixture f;
  MakeArray4(f, "arr");

  auto* idx = f.ctx.CreateVariable("idx", 8);
  idx->value = MakeAllX(f.arena, 8);

  auto* sel =
      MakeSelectExpr(f.arena, MakeId(f.arena, "arr"), MakeId(f.arena, "idx"));
  auto result = EvalExpr(sel, f.ctx, f.arena);
  EXPECT_FALSE(result.IsKnown());
}

TEST(ArrayIndexingAndSlicing, IndexedPartSelectSizeIsConstantPositionVaries) {
  // The size of a part-select is fixed by its constant width operand even when
  // the starting position comes from a runtime variable: the same '+:' select
  // yields a result of the constant width regardless of the variable base.
  SimFixture f;

  auto* vec = f.ctx.CreateVariable("vec", 32);
  vec->value = MakeLogic4VecVal(f.arena, 32, 0xAABBCCDDull);
  auto* pos = f.ctx.CreateVariable("pos", 32);
  pos->value = MakeLogic4VecVal(f.arena, 32, 8);

  auto result =
      EvalExpr(MkPlusPartSelect(f.arena, "vec", "pos", 8), f.ctx, f.arena);
  EXPECT_EQ(result.width, 8u);
  EXPECT_TRUE(result.IsKnown());
  EXPECT_EQ(result.ToUint64(), 0xCCu);

  // A different runtime position selects different bits but the width — the
  // constant size of the part-select — is unchanged.
  pos->value = MakeLogic4VecVal(f.arena, 32, 16);
  auto moved =
      EvalExpr(MkPlusPartSelect(f.arena, "vec", "pos", 8), f.ctx, f.arena);
  EXPECT_EQ(moved.width, 8u);
  EXPECT_EQ(moved.ToUint64(), 0xBBu);
}

TEST(ArrayIndexingAndSlicing, ReadSliceConcat) {
  SimFixture f;
  MakeArray4(f, "arr");

  auto result = EvalExpr(MkSlice(f.arena, "arr", 2, 1), f.ctx, f.arena);
  EXPECT_EQ(result.width, 16u);

  EXPECT_EQ(result.ToUint64(), (30u << 8) | 20u);
}

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

  auto* oob = f.ctx.FindVariable("arr[10]");
  EXPECT_EQ(oob, nullptr);

  auto after = EvalExpr(MakeSelect(f.arena, "arr", 1), f.ctx, f.arena);
  EXPECT_EQ(after.ToUint64(), 20u);
}

TEST(ArrayIndexingAndSlicing, ExecutedOutOfBoundsWriteLeavesArrayUnchanged) {
  // Driving an assignment whose index is out of bounds through the statement
  // execution path performs no operation: the in-range element keeps the value
  // it was given and the out-of-bounds element is never materialized.
  SimFixture f;
  auto* design = ElaborateSrc(
      "module t;\n"
      "  logic [7:0] mem [0:3];\n"
      "  initial begin\n"
      "    mem[1] = 8'd20;\n"
      "    mem[7] = 8'd99;\n"
      "  end\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  LowerAndRun(design, f);

  auto* in_range = f.ctx.FindVariable("mem[1]");
  ASSERT_NE(in_range, nullptr);
  EXPECT_EQ(in_range->value.ToUint64(), 20u);
  EXPECT_EQ(f.ctx.FindVariable("mem[7]"), nullptr);
}

TEST(ArrayIndexingAndSlicing, ExecutedUnknownIndexWriteIsNoop) {
  // An index expression carrying an x or z bit is invalid, so the write must do
  // nothing. In particular it must not fall through to a defined element (an x
  // index can numerically collapse to 0) and overwrite it.
  SimFixture f;
  auto* design = ElaborateSrc(
      "module t;\n"
      "  logic [7:0] mem [0:3];\n"
      "  logic [1:0] idx;\n"
      "  initial begin\n"
      "    mem[0] = 8'd10;\n"
      "    mem[1] = 8'd20;\n"
      "    idx = 2'bxx;\n"
      "    mem[idx] = 8'd99;\n"
      "  end\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  LowerAndRun(design, f);

  auto* e0 = f.ctx.FindVariable("mem[0]");
  auto* e1 = f.ctx.FindVariable("mem[1]");
  ASSERT_NE(e0, nullptr);
  ASSERT_NE(e1, nullptr);
  EXPECT_EQ(e0->value.ToUint64(), 10u);
  EXPECT_EQ(e1->value.ToUint64(), 20u);
}

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
