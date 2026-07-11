#include "builders_ast.h"
#include "fixture_simulator.h"
#include "simulator/evaluation.h"
#include "simulator/lowerer.h"
#include "simulator/variable.h"

using namespace delta;

namespace {

TEST(LvalueSim, VarLvalueCompoundAdd) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "module t;\n"
      "  int x;\n"
      "  initial begin x = 10; x += 5; end\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  Lowerer lowerer(f.ctx, f.arena, f.diag);
  lowerer.Lower(design);
  f.scheduler.Run();
  auto* var = f.ctx.FindVariable("x");
  ASSERT_NE(var, nullptr);
  EXPECT_EQ(var->value.ToUint64(), 15u);
}

TEST(CompoundAssignOpEval, LtLtLtEq) {
  SimFixture f;
  auto* var = f.ctx.CreateVariable("a", 32);
  var->value = MakeLogic4VecVal(f.arena, 32, 1);

  auto* expr = MakeBinary(f.arena, TokenKind::kLtLtLtEq, MakeId(f.arena, "a"),
                          MakeInt(f.arena, 4));
  auto result = EvalExpr(expr, f.ctx, f.arena);
  EXPECT_EQ(result.ToUint64(), 16u);
  EXPECT_EQ(var->value.ToUint64(), 16u);
}

TEST(CompoundAssignOpEval, GtGtGtEq) {
  SimFixture f;
  auto* var = f.ctx.CreateVariable("a", 32);
  var->value = MakeLogic4VecVal(f.arena, 32, 256);

  auto* expr = MakeBinary(f.arena, TokenKind::kGtGtGtEq, MakeId(f.arena, "a"),
                          MakeInt(f.arena, 4));
  auto result = EvalExpr(expr, f.ctx, f.arena);
  EXPECT_EQ(result.ToUint64(), 16u);
  EXPECT_EQ(var->value.ToUint64(), 16u);
}

TEST(LvalueSim, CompoundAssignWithIndexedLhs) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "module t;\n"
      "  int arr [0:3];\n"
      "  initial begin\n"
      "    arr[0] = 0; arr[1] = 0; arr[2] = 10; arr[3] = 0;\n"
      "    arr[2] += 5;\n"
      "  end\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  Lowerer lowerer(f.ctx, f.arena, f.diag);
  lowerer.Lower(design);
  f.scheduler.Run();
  auto* var = f.ctx.FindVariable("arr[2]");
  ASSERT_NE(var, nullptr);
  EXPECT_EQ(var->value.ToUint64(), 15u);
}

TEST(LvalueSim, CompoundAssignEvaluatesLvalueIndexOnce) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "module t;\n"
      "  int arr [0:3];\n"
      "  int idx_calls;\n"
      "  function automatic int idx_fn();\n"
      "    idx_calls = idx_calls + 1;\n"
      "    return 2;\n"
      "  endfunction\n"
      "  initial begin\n"
      "    arr[0] = 0; arr[1] = 0; arr[2] = 10; arr[3] = 0;\n"
      "    idx_calls = 0;\n"
      "    arr[idx_fn()] += 5;\n"
      "  end\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  Lowerer lowerer(f.ctx, f.arena, f.diag);
  lowerer.Lower(design);
  f.scheduler.Run();
  auto* arr = f.ctx.FindVariable("arr");
  auto* calls = f.ctx.FindVariable("idx_calls");
  ASSERT_NE(arr, nullptr);
  ASSERT_NE(calls, nullptr);
  auto* arr_elem = f.ctx.FindVariable("arr[2]");
  ASSERT_NE(arr_elem, nullptr);
  EXPECT_EQ(arr_elem->value.ToUint64(), 15u);
  EXPECT_EQ(calls->value.ToUint64(), 1u);
}

// §11.4.1: the once-only left-hand index rule applies to a packed bit-select
// lhs too, not just an unpacked array element. `data[idx_fn()] += ...` reads
// and writes the same bit of a single packed variable, and each of those steps
// re-derives the bit from the index expression; the side-effecting index must
// still be evaluated exactly once.
TEST(LvalueSim, CompoundAssignBitSelectIndexEvaluatedOnce) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "module t;\n"
      "  logic [7:0] data;\n"
      "  int idx_calls;\n"
      "  function automatic int idx_fn();\n"
      "    idx_calls = idx_calls + 1;\n"
      "    return 3;\n"
      "  endfunction\n"
      "  initial begin\n"
      "    data = 8'b0000_0000;\n"
      "    idx_calls = 0;\n"
      "    data[idx_fn()] += 1'b1;\n"
      "  end\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  Lowerer lowerer(f.ctx, f.arena, f.diag);
  lowerer.Lower(design);
  f.scheduler.Run();
  auto* data = f.ctx.FindVariable("data");
  auto* calls = f.ctx.FindVariable("idx_calls");
  ASSERT_NE(data, nullptr);
  ASSERT_NE(calls, nullptr);
  EXPECT_EQ(data->value.ToUint64(), 0x08u);
  EXPECT_EQ(calls->value.ToUint64(), 1u);
}

// §11.4.1: the once-only rule also governs an indexed part-select lhs
// (`data[f() +: w] += ...`). That lhs resolves through a different production
// path (packed part-select read + write) than a plain bit-select, and the base
// index is re-derived by both the read and the write, so a side-effecting base
// index must be evaluated exactly once here as well.
TEST(LvalueSim, CompoundAssignPartSelectBaseIndexEvaluatedOnce) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "module t;\n"
      "  logic [7:0] data;\n"
      "  int idx_calls;\n"
      "  function automatic int idx_fn();\n"
      "    idx_calls = idx_calls + 1;\n"
      "    return 2;\n"
      "  endfunction\n"
      "  initial begin\n"
      "    data = 8'b0000_0000;\n"
      "    idx_calls = 0;\n"
      "    data[idx_fn() +: 2] += 2'b11;\n"
      "  end\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  Lowerer lowerer(f.ctx, f.arena, f.diag);
  lowerer.Lower(design);
  f.scheduler.Run();
  auto* data = f.ctx.FindVariable("data");
  auto* calls = f.ctx.FindVariable("idx_calls");
  ASSERT_NE(data, nullptr);
  ASSERT_NE(calls, nullptr);
  EXPECT_EQ(data->value.ToUint64(), 0x0Cu);
  EXPECT_EQ(calls->value.ToUint64(), 1u);
}

// §11.4.1: the blocking-assignment equivalence also holds when the lhs is a
// struct member (`s.field op= rhs`). That lhs kind takes its own production
// branch (member-access read + struct-field write) distinct from a plain
// variable or a select, so exercise `s.lo += 3` end-to-end from a real packed
// struct declaration and confirm only the addressed field is updated.
TEST(LvalueSim, CompoundAssignStructMemberLhs) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "module t;\n"
      "  typedef struct packed {\n"
      "    logic [3:0] hi;\n"
      "    logic [3:0] lo;\n"
      "  } pair_t;\n"
      "  pair_t s;\n"
      "  initial begin\n"
      "    s.hi = 4'd2;\n"
      "    s.lo = 4'd5;\n"
      "    s.lo += 4'd3;\n"
      "  end\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  Lowerer lowerer(f.ctx, f.arena, f.diag);
  lowerer.Lower(design);
  f.scheduler.Run();
  auto* s = f.ctx.FindVariable("s");
  ASSERT_NE(s, nullptr);
  // hi keeps 2 in the high nibble; lo becomes 5 + 3 = 8 in the low nibble.
  EXPECT_EQ(s->value.ToUint64(), 0x28u);
}

TEST(LvalueSim, CompoundAssignSelfReferenceDoublesValue) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "module t;\n"
      "  int a;\n"
      "  initial begin\n"
      "    a = 5;\n"
      "    a += a;\n"
      "  end\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  Lowerer lowerer(f.ctx, f.arena, f.diag);
  lowerer.Lower(design);
  f.scheduler.Run();
  auto* var = f.ctx.FindVariable("a");
  ASSERT_NE(var, nullptr);
  EXPECT_EQ(var->value.ToUint64(), 10u);
}

TEST(LvalueSim, CompoundAssignArithBitwiseShiftThroughPipeline) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "module t;\n"
      "  int sub, mul, divr, mod;\n"
      "  int band, bor, bxor;\n"
      "  int shl, shr;\n"
      "  initial begin\n"
      "    sub = 10;  sub  -= 3;\n"
      "    mul = 6;   mul  *= 2;\n"
      "    divr = 8;  divr /= 2;\n"
      "    mod = 17;  mod  %= 5;\n"
      "    band = 'hFF; band &= 'h0F;\n"
      "    bor  = 'h01; bor  |= 'h10;\n"
      "    bxor = 'hAA; bxor ^= 'hFF;\n"
      "    shl = 1;   shl  <<= 4;\n"
      "    shr = 256; shr  >>= 4;\n"
      "  end\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  Lowerer lowerer(f.ctx, f.arena, f.diag);
  lowerer.Lower(design);
  f.scheduler.Run();
  EXPECT_EQ(f.ctx.FindVariable("sub")->value.ToUint64(), 7u);
  EXPECT_EQ(f.ctx.FindVariable("mul")->value.ToUint64(), 12u);
  EXPECT_EQ(f.ctx.FindVariable("divr")->value.ToUint64(), 4u);
  EXPECT_EQ(f.ctx.FindVariable("mod")->value.ToUint64(), 2u);
  EXPECT_EQ(f.ctx.FindVariable("band")->value.ToUint64(), 0x0Fu);
  EXPECT_EQ(f.ctx.FindVariable("bor")->value.ToUint64(), 0x11u);
  EXPECT_EQ(f.ctx.FindVariable("bxor")->value.ToUint64(), 0x55u);
  EXPECT_EQ(f.ctx.FindVariable("shl")->value.ToUint64(), 16u);
  EXPECT_EQ(f.ctx.FindVariable("shr")->value.ToUint64(), 16u);
}

}  // namespace
