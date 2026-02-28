// §11.5.1: Vector bit-select and part-select addressing

#include "builders_ast.h"
#include "fixture_simulator.h"
#include "helpers_eval_op.h"
#include "parser/ast.h"
#include "simulator/eval.h"
#include "simulator/sim_context.h"  // StructTypeInfo, StructFieldInfo

using namespace delta;

namespace {

// ==========================================================================
// Part-select partial OOB — §11.5.1
// ==========================================================================
TEST(EvalAdv, PartSelectPartialOOB) {
  SimFixture f;
  // §11.5.1: v[6 +: 4] on 8-bit var → bits 6,7 valid, bits 8,9 OOB → X.
  MakeVar(f, "ov", 8, 0xFF);
  auto* sel = f.arena.Create<Expr>();
  sel->kind = ExprKind::kSelect;
  sel->base = MakeId(f.arena, "ov");
  sel->index = MakeInt(f.arena, 6);
  sel->index_end = MakeInt(f.arena, 4);
  sel->is_part_select_plus = true;
  auto result = EvalExpr(sel, f.ctx, f.arena);
  EXPECT_EQ(result.width, 4u);
  // Bits 0,1 (= original bits 6,7) should be 1 (known).
  EXPECT_EQ(result.words[0].aval & 0x3u, 0x3u);
  // Bits 2,3 (= original bits 8,9) should be X (bval set).
  EXPECT_NE(result.words[0].bval & 0xCu, 0u);
}

// ==========================================================================
// §7.4.5: X/Z address on array gives OOB (X) value
// ==========================================================================
TEST(EvalAdv, ArrayXZAddrReturnsX) {
  SimFixture f;
  // arr[0]=0x11, arr[1]=0x22 (8-bit elements).
  MakeVar(f, "arr4[0]", 8, 0x11);
  MakeVar(f, "arr4[1]", 8, 0x22);
  ArrayInfo info{};
  info.lo = 0;
  info.size = 2;
  info.elem_width = 8;
  f.ctx.RegisterArray("arr4", info);

  // arr4[x] — X address should return X.
  auto* sel = f.arena.Create<Expr>();
  sel->kind = ExprKind::kSelect;
  sel->base = MakeId(f.arena, "arr4");
  // Create an X-valued index.
  auto* idx = MakeInt(f.arena, 0);
  sel->index = idx;
  // Manually set bval to make it X.
  // Evaluate: since we can't directly set bval on a literal,
  // create a variable with X value and use it.
  auto* xvar = f.ctx.CreateVariable("xidx", 8);
  xvar->value = MakeLogic4Vec(f.arena, 8);
  xvar->value.words[0].aval = 1;
  xvar->value.words[0].bval = 1;  // aval=1, bval=1 → X
  sel->index = MakeId(f.arena, "xidx");

  auto result = EvalExpr(sel, f.ctx, f.arena);
  // X/Z address → result should be X (bval != 0).
  EXPECT_NE(result.nwords, 0u);
  EXPECT_NE(result.words[0].bval, 0u);
}

// ==========================================================================
// Bit-select/part-select X/Z address — §11.5.1
// ==========================================================================
TEST(EvalOpXZ, BitSelectXAddr) {
  SimFixture f;
  // v[x] should return 1'bx when index is unknown.
  auto* v = f.ctx.CreateVariable("bsv", 8);
  v->value = MakeLogic4VecVal(f.arena, 8, 0xAB);
  MakeVar4(f, "bsi", 4, 0, 1);  // 4'bx (unknown index)
  auto* sel = f.arena.Create<Expr>();
  sel->kind = ExprKind::kSelect;
  sel->base = MakeId(f.arena, "bsv");
  sel->index = MakeId(f.arena, "bsi");
  auto result = EvalExpr(sel, f.ctx, f.arena);
  EXPECT_EQ(result.width, 1u);
  EXPECT_NE(result.words[0].bval, 0u);  // result is x
}

TEST(EvalOpXZ, PartSelectXAddr) {
  SimFixture f;
  // v[x +: 4] should return all-x when base index is unknown.
  auto* v = f.ctx.CreateVariable("psv", 8);
  v->value = MakeLogic4VecVal(f.arena, 8, 0xAB);
  MakeVar4(f, "psi", 4, 0, 1);  // unknown index
  auto* sel = f.arena.Create<Expr>();
  sel->kind = ExprKind::kSelect;
  sel->base = MakeId(f.arena, "psv");
  sel->index = MakeId(f.arena, "psi");
  sel->index_end = MakeInt(f.arena, 4);
  sel->is_part_select_plus = true;
  auto result = EvalExpr(sel, f.ctx, f.arena);
  EXPECT_EQ(result.width, 4u);
  EXPECT_NE(result.words[0].bval, 0u);  // result has x bits
}

// § constant_range — part select
TEST(SimA83, PartSelectRange) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "module t;\n"
      "  logic [7:0] data;\n"
      "  logic [3:0] x;\n"
      "  initial begin\n"
      "    data = 8'hA5;\n"
      "    x = data[3:0];\n"
      "  end\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  Lowerer lowerer(f.ctx, f.arena, f.diag);
  lowerer.Lower(design);
  f.scheduler.Run();
  auto* var = f.ctx.FindVariable("x");
  ASSERT_NE(var, nullptr);
  EXPECT_EQ(var->value.ToUint64(), 0x5u);
}

// § indexed_range — plus-colon indexed part select
TEST(SimA83, IndexedPartSelectPlus) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "module t;\n"
      "  logic [7:0] data;\n"
      "  logic [3:0] x;\n"
      "  initial begin\n"
      "    data = 8'hA5;\n"
      "    x = data[0+:4];\n"
      "  end\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  Lowerer lowerer(f.ctx, f.arena, f.diag);
  lowerer.Lower(design);
  f.scheduler.Run();
  auto* var = f.ctx.FindVariable("x");
  ASSERT_NE(var, nullptr);
  EXPECT_EQ(var->value.ToUint64(), 0x5u);
}

// § indexed_range — minus-colon indexed part select
TEST(SimA83, IndexedPartSelectMinus) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "module t;\n"
      "  logic [7:0] data;\n"
      "  logic [3:0] x;\n"
      "  initial begin\n"
      "    data = 8'hA5;\n"
      "    x = data[7-:4];\n"
      "  end\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  Lowerer lowerer(f.ctx, f.arena, f.diag);
  lowerer.Lower(design);
  f.scheduler.Run();
  auto* var = f.ctx.FindVariable("x");
  ASSERT_NE(var, nullptr);
  EXPECT_EQ(var->value.ToUint64(), 0xAu);
}

// § primary — bit_select
TEST(SimA84, PrimaryBitSelect) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "module t;\n"
      "  logic [7:0] data;\n"
      "  logic x;\n"
      "  initial begin data = 8'b10101010; x = data[1]; end\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  Lowerer lowerer(f.ctx, f.arena, f.diag);
  lowerer.Lower(design);
  f.scheduler.Run();
  auto* var = f.ctx.FindVariable("x");
  ASSERT_NE(var, nullptr);
  EXPECT_EQ(var->value.ToUint64(), 1u);
}

// § primary — part_select_range (constant range)
TEST(SimA84, PrimaryPartSelectRange) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "module t;\n"
      "  logic [15:0] data;\n"
      "  logic [7:0] x;\n"
      "  initial begin data = 16'hABCD; x = data[15:8]; end\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  Lowerer lowerer(f.ctx, f.arena, f.diag);
  lowerer.Lower(design);
  f.scheduler.Run();
  auto* var = f.ctx.FindVariable("x");
  ASSERT_NE(var, nullptr);
  EXPECT_EQ(var->value.ToUint64(), 0xABu);
}

// § primary — indexed part select (plus)
TEST(SimA84, PrimaryIndexedPartSelectPlus) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "module t;\n"
      "  logic [15:0] data;\n"
      "  logic [7:0] x;\n"
      "  initial begin data = 16'hABCD; x = data[8+:8]; end\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  Lowerer lowerer(f.ctx, f.arena, f.diag);
  lowerer.Lower(design);
  f.scheduler.Run();
  auto* var = f.ctx.FindVariable("x");
  ASSERT_NE(var, nullptr);
  EXPECT_EQ(var->value.ToUint64(), 0xABu);
}

// § primary — indexed part select (minus)
TEST(SimA84, PrimaryIndexedPartSelectMinus) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "module t;\n"
      "  logic [15:0] data;\n"
      "  logic [7:0] x;\n"
      "  initial begin data = 16'hABCD; x = data[15-:8]; end\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  Lowerer lowerer(f.ctx, f.arena, f.diag);
  lowerer.Lower(design);
  f.scheduler.Run();
  auto* var = f.ctx.FindVariable("x");
  ASSERT_NE(var, nullptr);
  EXPECT_EQ(var->value.ToUint64(), 0xABu);
}

// § variable_lvalue — bit select blocking assignment
TEST(SimA85, VarLvalueBitSelect) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "module t;\n"
      "  logic [7:0] x;\n"
      "  initial begin x = 8'h00; x[3] = 1; end\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  Lowerer lowerer(f.ctx, f.arena, f.diag);
  lowerer.Lower(design);
  f.scheduler.Run();
  auto* var = f.ctx.FindVariable("x");
  ASSERT_NE(var, nullptr);
  EXPECT_EQ(var->value.ToUint64(), 0x08u);
}

// § variable_lvalue — indexed part select + blocking assignment
TEST(SimA85, VarLvalueIndexedPartSelectPlus) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "module t;\n"
      "  logic [15:0] x;\n"
      "  initial begin x = 16'h0000; x[8+:8] = 8'hAB; end\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  Lowerer lowerer(f.ctx, f.arena, f.diag);
  lowerer.Lower(design);
  f.scheduler.Run();
  auto* var = f.ctx.FindVariable("x");
  ASSERT_NE(var, nullptr);
  EXPECT_EQ(var->value.ToUint64(), 0xAB00u);
}

// § variable_lvalue — indexed part select - blocking assignment
TEST(SimA85, VarLvalueIndexedPartSelectMinus) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "module t;\n"
      "  logic [15:0] x;\n"
      "  initial begin x = 16'h0000; x[15-:8] = 8'hCD; end\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  Lowerer lowerer(f.ctx, f.arena, f.diag);
  lowerer.Lower(design);
  f.scheduler.Run();
  auto* var = f.ctx.FindVariable("x");
  ASSERT_NE(var, nullptr);
  EXPECT_EQ(var->value.ToUint64(), 0xCD00u);
}

}  // namespace
