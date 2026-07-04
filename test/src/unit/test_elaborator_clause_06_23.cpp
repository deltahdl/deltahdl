#include "fixture_simulator.h"
#include "helpers_generate_elab.h"
#include "simulator/lowerer.h"
#include "simulator/variable.h"

using namespace delta;

namespace {

// Counts variables in `mod` whose name ends in `last`. A declaration inside an
// (unnamed) generate block reaches the module's variable list under a scoped
// name, so the trailing character identifies which alternative was taken.
int CountVarsEndingWith(const RtlirModule* mod, char last) {
  int count = 0;
  for (const auto& var : mod->variables) {
    if (!var.name.empty() && var.name.back() == last) ++count;
  }
  return count;
}

TEST(TypeOperatorSim, TypeOpInt) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "module t;\n"
      "  int a;\n"
      "  var type(a) b;\n"
      "  initial begin\n"
      "    a = 42;\n"
      "    b = 99;\n"
      "  end\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);

  Lowerer lowerer(f.ctx, f.arena, f.diag);
  lowerer.Lower(design);
  f.scheduler.Run();

  auto* var = f.ctx.FindVariable("b");
  ASSERT_NE(var, nullptr);
  EXPECT_EQ(var->value.width, 32u);
  EXPECT_EQ(var->value.ToUint64(), 99u);
  EXPECT_TRUE(var->is_signed);
}

TEST(TypeOperatorSim, TypeOpLogic) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "module t;\n"
      "  logic a;\n"
      "  var type(a) b;\n"
      "  initial begin\n"
      "    a = 1;\n"
      "    b = 1;\n"
      "  end\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);

  Lowerer lowerer(f.ctx, f.arena, f.diag);
  lowerer.Lower(design);
  f.scheduler.Run();

  auto* var = f.ctx.FindVariable("b");
  ASSERT_NE(var, nullptr);
  EXPECT_EQ(var->value.width, 1u);
  EXPECT_EQ(var->value.ToUint64(), 1u);
  EXPECT_FALSE(var->is_signed);
}

TEST(TypeOperatorSim, TypeOpByte) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "module t;\n"
      "  byte a;\n"
      "  var type(a) b;\n"
      "  initial begin\n"
      "    a = 8'hAB;\n"
      "    b = 8'hCD;\n"
      "  end\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);

  Lowerer lowerer(f.ctx, f.arena, f.diag);
  lowerer.Lower(design);
  f.scheduler.Run();

  auto* var = f.ctx.FindVariable("b");
  ASSERT_NE(var, nullptr);
  EXPECT_EQ(var->value.width, 8u);
  EXPECT_EQ(var->value.ToUint64(), 0xCDu);
  EXPECT_TRUE(var->is_signed);
}

TEST(TypeOperatorSim, TypeOpShortint) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "module t;\n"
      "  shortint a;\n"
      "  var type(a) b;\n"
      "  initial begin\n"
      "    a = 16'h1234;\n"
      "    b = 16'hABCD;\n"
      "  end\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);

  Lowerer lowerer(f.ctx, f.arena, f.diag);
  lowerer.Lower(design);
  f.scheduler.Run();

  auto* var = f.ctx.FindVariable("b");
  ASSERT_NE(var, nullptr);
  EXPECT_EQ(var->value.width, 16u);
  EXPECT_EQ(var->value.ToUint64(), 0xABCDu);
  EXPECT_TRUE(var->is_signed);
}

TEST(TypeOperatorSim, TypeOpLongint) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "module t;\n"
      "  longint a;\n"
      "  var type(a) b;\n"
      "  initial begin\n"
      "    a = 64'hDEAD_BEEF_CAFE_BABE;\n"
      "    b = 64'h0123_4567_89AB_CDEF;\n"
      "  end\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);

  Lowerer lowerer(f.ctx, f.arena, f.diag);
  lowerer.Lower(design);
  f.scheduler.Run();

  auto* var = f.ctx.FindVariable("b");
  ASSERT_NE(var, nullptr);
  EXPECT_EQ(var->value.width, 64u);
  EXPECT_EQ(var->value.ToUint64(), 0x0123456789ABCDEFu);
  EXPECT_TRUE(var->is_signed);
}

TEST(TypeOperatorSim, TypeOpInteger) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "module t;\n"
      "  integer a;\n"
      "  var type(a) b;\n"
      "  initial begin\n"
      "    a = 32'hDEAD;\n"
      "    b = 32'hBEEF;\n"
      "  end\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);

  Lowerer lowerer(f.ctx, f.arena, f.diag);
  lowerer.Lower(design);
  f.scheduler.Run();

  auto* var = f.ctx.FindVariable("b");
  ASSERT_NE(var, nullptr);
  EXPECT_EQ(var->value.width, 32u);
  EXPECT_EQ(var->value.ToUint64(), 0xBEEFu);
  EXPECT_TRUE(var->is_signed);
}

TEST(TypeOperatorSim, TypeOpReal) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "module t;\n"
      "  real a;\n"
      "  var type(a) b;\n"
      "  initial begin\n"
      "    a = 3.14;\n"
      "    b = 2.71;\n"
      "  end\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);

  Lowerer lowerer(f.ctx, f.arena, f.diag);
  lowerer.Lower(design);
  f.scheduler.Run();

  auto* var = f.ctx.FindVariable("b");
  ASSERT_NE(var, nullptr);
  EXPECT_EQ(var->value.width, 64u);
}

TEST(TypeOperatorSim, TypeOpPreservesSignedInt) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "module t;\n"
      "  int a;\n"
      "  var type(a) result;\n"
      "  initial result = -1;\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);

  Lowerer lowerer(f.ctx, f.arena, f.diag);
  lowerer.Lower(design);
  f.scheduler.Run();

  auto* var = f.ctx.FindVariable("result");
  ASSERT_NE(var, nullptr);
  EXPECT_TRUE(var->is_signed);

  EXPECT_EQ(var->value.ToUint64(), 0xFFFFFFFFu);
}

TEST(TypeOperatorSim, TypeOpWidthTruncation) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "module t;\n"
      "  byte a;\n"
      "  var type(a) result;\n"
      "  initial result = 32'hFFFF;\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);

  Lowerer lowerer(f.ctx, f.arena, f.diag);
  lowerer.Lower(design);
  f.scheduler.Run();

  auto* var = f.ctx.FindVariable("result");
  ASSERT_NE(var, nullptr);
  EXPECT_EQ(var->value.width, 8u);

  EXPECT_EQ(var->value.ToUint64(), 0xFFu);
}

static void LowerRunAndCompareWidths(SimFixture& f, RtlirDesign* design,
                                     Variable*& va_out, Variable*& vb_out) {
  Lowerer lowerer(f.ctx, f.arena, f.diag);
  lowerer.Lower(design);
  f.scheduler.Run();
  va_out = f.ctx.FindVariable("a");
  vb_out = f.ctx.FindVariable("b");
  ASSERT_NE(va_out, nullptr);
  ASSERT_NE(vb_out, nullptr);
  EXPECT_EQ(va_out->value.width, vb_out->value.width);
}

TEST(TypeOperatorSim, TypeOpIntDifferentValues) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "module t;\n"
      "  int a;\n"
      "  var type(a) b;\n"
      "  initial begin\n"
      "    a = 1000;\n"
      "    b = 2000;\n"
      "  end\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);

  Variable* va = nullptr;
  Variable* vb = nullptr;
  LowerRunAndCompareWidths(f, design, va, vb);
  EXPECT_EQ(va->value.ToUint64(), 1000u);
  EXPECT_EQ(vb->value.ToUint64(), 2000u);
}

TEST(TypeOperatorSim, TypeOpShortintSignExtension) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "module t;\n"
      "  shortint a;\n"
      "  var type(a) result;\n"
      "  int wide;\n"
      "  initial begin\n"
      "    a = -1;\n"
      "    result = a;\n"
      "    wide = result;\n"
      "  end\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);

  Lowerer lowerer(f.ctx, f.arena, f.diag);
  lowerer.Lower(design);
  f.scheduler.Run();

  auto* var = f.ctx.FindVariable("result");
  ASSERT_NE(var, nullptr);
  EXPECT_EQ(var->value.width, 16u);
  EXPECT_TRUE(var->is_signed);

  EXPECT_EQ(var->value.ToUint64(), 0xFFFFu);
}

TEST(TypeOperatorSim, TypeOpParameterTypeDefault) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "module t;\n"
      "  parameter type T = int;\n"
      "  T x;\n"
      "  var type(x) result;\n"
      "  initial begin\n"
      "    x = 42;\n"
      "    result = 77;\n"
      "  end\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);

  Lowerer lowerer(f.ctx, f.arena, f.diag);
  lowerer.Lower(design);
  f.scheduler.Run();

  auto* var = f.ctx.FindVariable("result");
  ASSERT_NE(var, nullptr);
  EXPECT_EQ(var->value.width, 32u);
  EXPECT_EQ(var->value.ToUint64(), 77u);
}

TEST(TypeOperatorSim, TypeOpEnumType) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "module t;\n"
      "  typedef enum {RED, GREEN, BLUE} color_t;\n"
      "  color_t c;\n"
      "  var type(c) result;\n"
      "  initial begin\n"
      "    c = GREEN;\n"
      "    result = 2;\n"
      "  end\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);

  Lowerer lowerer(f.ctx, f.arena, f.diag);
  lowerer.Lower(design);
  f.scheduler.Run();

  auto* var = f.ctx.FindVariable("result");
  ASSERT_NE(var, nullptr);

  EXPECT_EQ(var->value.width, 32u);
  EXPECT_EQ(var->value.ToUint64(), 2u);
}

TEST(TypeOperatorSim, TypeOpIntOverflow) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "module t;\n"
      "  int a;\n"
      "  var type(a) result;\n"
      "  initial result = 64'hFFFF_FFFF_1234_5678;\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);

  Lowerer lowerer(f.ctx, f.arena, f.diag);
  lowerer.Lower(design);
  f.scheduler.Run();

  auto* var = f.ctx.FindVariable("result");
  ASSERT_NE(var, nullptr);
  EXPECT_EQ(var->value.width, 32u);

  EXPECT_EQ(var->value.ToUint64(), 0x12345678u);
}

TEST(TypeOperatorSim, TypeOpMatchingWidths) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "module t;\n"
      "  int a;\n"
      "  var type(a) b;\n"
      "  initial begin\n"
      "    a = 0;\n"
      "    b = 0;\n"
      "  end\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);

  Variable* va = nullptr;
  Variable* vb = nullptr;
  LowerRunAndCompareWidths(f, design, va, vb);
  EXPECT_EQ(va->is_signed, vb->is_signed);
}

TEST(TypeOperatorSim, TypeOpLongintMaxValue) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "module t;\n"
      "  longint a;\n"
      "  var type(a) result;\n"
      "  initial result = 64'h7FFF_FFFF_FFFF_FFFF;\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);

  Lowerer lowerer(f.ctx, f.arena, f.diag);
  lowerer.Lower(design);
  f.scheduler.Run();

  auto* var = f.ctx.FindVariable("result");
  ASSERT_NE(var, nullptr);
  EXPECT_EQ(var->value.width, 64u);
  EXPECT_EQ(var->value.ToUint64(), 0x7FFFFFFFFFFFFFFFu);
  EXPECT_TRUE(var->is_signed);
}

TEST(TypeOperatorSim, TypeOpShortintZero) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "module t;\n"
      "  shortint a;\n"
      "  var type(a) result;\n"
      "  initial result = 0;\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);

  Lowerer lowerer(f.ctx, f.arena, f.diag);
  lowerer.Lower(design);
  f.scheduler.Run();

  auto* var = f.ctx.FindVariable("result");
  ASSERT_NE(var, nullptr);
  EXPECT_EQ(var->value.width, 16u);
  EXPECT_EQ(var->value.ToUint64(), 0u);
  EXPECT_TRUE(var->is_signed);
}

TEST(TypeOperatorSim, TypeOpByteArithmeticSigned) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "module t;\n"
      "  byte a;\n"
      "  var type(a) result;\n"
      "  initial begin\n"
      "    a = 100;\n"
      "    result = a + 8'd55;\n"
      "  end\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);

  Lowerer lowerer(f.ctx, f.arena, f.diag);
  lowerer.Lower(design);
  f.scheduler.Run();

  auto* var = f.ctx.FindVariable("result");
  ASSERT_NE(var, nullptr);
  EXPECT_EQ(var->value.width, 8u);
  EXPECT_TRUE(var->is_signed);

  EXPECT_EQ(var->value.ToUint64(), 155u);
}

TEST(TypeOperatorSim, TypeOpChainedTypeRef) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "module t;\n"
      "  int a;\n"
      "  var type(a) b;\n"
      "  var type(b) c;\n"
      "  initial begin\n"
      "    a = 10;\n"
      "    b = 20;\n"
      "    c = 30;\n"
      "  end\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);

  Lowerer lowerer(f.ctx, f.arena, f.diag);
  lowerer.Lower(design);
  f.scheduler.Run();

  auto* vc = f.ctx.FindVariable("c");
  ASSERT_NE(vc, nullptr);
  EXPECT_EQ(vc->value.width, 32u);
  EXPECT_EQ(vc->value.ToUint64(), 30u);
  EXPECT_TRUE(vc->is_signed);
}

TEST(TypeOperatorSim, TypeOpMultipleAssignments) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "module t;\n"
      "  int a;\n"
      "  var type(a) result;\n"
      "  initial begin\n"
      "    result = 1;\n"
      "    result = 2;\n"
      "    result = 3;\n"
      "  end\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);

  Lowerer lowerer(f.ctx, f.arena, f.diag);
  lowerer.Lower(design);
  f.scheduler.Run();

  auto* var = f.ctx.FindVariable("result");
  ASSERT_NE(var, nullptr);
  EXPECT_EQ(var->value.width, 32u);
  EXPECT_EQ(var->value.ToUint64(), 3u);
}

TEST(TypeOperatorSim, TypeOpShortintMaxUnsigned) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "module t;\n"
      "  shortint a;\n"
      "  var type(a) result;\n"
      "  initial result = 16'hFFFF;\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);

  Lowerer lowerer(f.ctx, f.arena, f.diag);
  lowerer.Lower(design);
  f.scheduler.Run();

  auto* var = f.ctx.FindVariable("result");
  ASSERT_NE(var, nullptr);
  EXPECT_EQ(var->value.width, 16u);
  EXPECT_EQ(var->value.ToUint64(), 0xFFFFu);
  EXPECT_TRUE(var->is_signed);
}

TEST(TypeOperatorSim, TypeOpByteFromWiderAssignment) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "module t;\n"
      "  byte a;\n"
      "  var type(a) result;\n"
      "  int wide;\n"
      "  initial begin\n"
      "    wide = 32'h12345678;\n"
      "    result = wide;\n"
      "  end\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);

  Lowerer lowerer(f.ctx, f.arena, f.diag);
  lowerer.Lower(design);
  f.scheduler.Run();

  auto* var = f.ctx.FindVariable("result");
  ASSERT_NE(var, nullptr);
  EXPECT_EQ(var->value.width, 8u);

  EXPECT_EQ(var->value.ToUint64(), 0x78u);
  EXPECT_TRUE(var->is_signed);
}

TEST(TypeOperatorSim, TypeOpLocalparamType) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "module t;\n"
      "  localparam type T = type(int);\n"
      "  T x;\n"
      "  initial x = 55;\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);

  Lowerer lowerer(f.ctx, f.arena, f.diag);
  lowerer.Lower(design);
  f.scheduler.Run();

  auto* var = f.ctx.FindVariable("x");
  ASSERT_NE(var, nullptr);
  EXPECT_EQ(var->value.width, 32u);
  EXPECT_EQ(var->value.ToUint64(), 55u);
  EXPECT_TRUE(var->is_signed);
}

TEST(TypeOperatorSim, TypeOpLogicVector) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "module t;\n"
      "  logic [15:0] a;\n"
      "  var type(a) b;\n"
      "  initial begin\n"
      "    a = 16'hBEEF;\n"
      "    b = 16'hCAFE;\n"
      "  end\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);

  Lowerer lowerer(f.ctx, f.arena, f.diag);
  lowerer.Lower(design);
  f.scheduler.Run();

  auto* var = f.ctx.FindVariable("b");
  ASSERT_NE(var, nullptr);
  EXPECT_EQ(var->value.width, 16u);
  EXPECT_EQ(var->value.ToUint64(), 0xCAFEu);
}

TEST(TypeOperatorSim, TypeOpWireNetDecl) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "module t;\n"
      "  wire [7:0] x;\n"
      "  wire type(x) y;\n"
      "  assign x = 8'hAB;\n"
      "  assign y = 8'hCD;\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);

  Lowerer lowerer(f.ctx, f.arena, f.diag);
  lowerer.Lower(design);
  f.scheduler.Run();

  auto* var = f.ctx.FindVariable("y");
  ASSERT_NE(var, nullptr);
  EXPECT_EQ(var->value.width, 8u);
  EXPECT_EQ(var->value.ToUint64(), 0xCDu);
}

TEST(TypeOperatorSim, TypeOpSelfDeterminedBinaryWidth) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "module t;\n"
      "  byte a;\n"
      "  int b;\n"
      "  var type(a + b) c;\n"
      "  initial begin\n"
      "    a = 1;\n"
      "    b = 2;\n"
      "    c = 32'hDEAD_BEEF;\n"
      "  end\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);

  Lowerer lowerer(f.ctx, f.arena, f.diag);
  lowerer.Lower(design);
  f.scheduler.Run();

  auto* var = f.ctx.FindVariable("c");
  ASSERT_NE(var, nullptr);
  EXPECT_EQ(var->value.width, 32u);
  EXPECT_EQ(var->value.ToUint64(), 0xDEADBEEFu);
}

TEST(TypeOperatorSim, TypeOpBitTypeUnsigned) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "module t;\n"
      "  bit [7:0] a;\n"
      "  var type(a) b;\n"
      "  initial begin\n"
      "    a = 8'hFF;\n"
      "    b = 8'hAB;\n"
      "  end\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);

  Lowerer lowerer(f.ctx, f.arena, f.diag);
  lowerer.Lower(design);
  f.scheduler.Run();

  auto* var = f.ctx.FindVariable("b");
  ASSERT_NE(var, nullptr);
  EXPECT_EQ(var->value.width, 8u);
  EXPECT_FALSE(var->is_signed);
  EXPECT_EQ(var->value.ToUint64(), 0xABu);
}

// §6.23 — the type operator applied to an expression yields that expression's
// self-determined type. Here the operand's type is produced by a user-defined
// typedef (§6.18) built from real source syntax: `bus_t` names a 24-bit logic
// vector, so `type(x)` derives a 24-bit unsigned type for the dependent
// declaration. Driven through the full pipeline and observed at runtime.
TEST(TypeOperatorSim, TypeOpTypedefVectorType) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "module t;\n"
      "  typedef logic [23:0] bus_t;\n"
      "  bus_t x;\n"
      "  var type(x) y;\n"
      "  initial begin\n"
      "    x = 24'h123456;\n"
      "    y = 24'hABCDEF;\n"
      "  end\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);

  Lowerer lowerer(f.ctx, f.arena, f.diag);
  lowerer.Lower(design);
  f.scheduler.Run();

  auto* var = f.ctx.FindVariable("y");
  ASSERT_NE(var, nullptr);
  EXPECT_EQ(var->value.width, 24u);
  EXPECT_FALSE(var->is_signed);
  EXPECT_EQ(var->value.ToUint64(), 0xABCDEFu);
}

TEST(TypeOperatorElab, TypeOfThisInClassMethodAccepted) {
  EXPECT_TRUE(
      ElabOk("class C;\n"
             "  static function type(this) get();\n"
             "    return null;\n"
             "  endfunction\n"
             "endclass\n"
             "module m;\n"
             "  C c;\n"
             "endmodule\n"));
}

TEST(TypeOperatorElab, TypeRefComparedToIntegerLiteralRejected) {
  EXPECT_FALSE(
      ElabOk("module m #(parameter type T = int) ();\n"
             "  initial begin\n"
             "    if (type(T) == 5) $stop;\n"
             "  end\n"
             "endmodule\n"));
}

TEST(TypeOperatorElab, TypeRefComparedToTypeRefAccepted) {
  EXPECT_TRUE(
      ElabOk("module m #(parameter type T = int) ();\n"
             "  initial begin\n"
             "    if (type(T) == type(int)) $stop;\n"
             "  end\n"
             "endmodule\n"));
}

TEST(TypeOperatorElab, NonTypeRefSideOfCaseEqRejected) {
  EXPECT_FALSE(
      ElabOk("module m #(parameter type T = int) ();\n"
             "  initial begin\n"
             "    if (type(T) === 0) $stop;\n"
             "  end\n"
             "endmodule\n"));
}

TEST(TypeOperatorElab, TypeRefComparedToVariableRejected) {
  EXPECT_FALSE(
      ElabOk("module m #(parameter type T = int) ();\n"
             "  int v;\n"
             "  initial begin\n"
             "    if (type(T) != v) $stop;\n"
             "  end\n"
             "endmodule\n"));
}

// The §6.23 rule is symmetric: a non-type-reference operand is rejected
// whether it appears on the left or the right of the comparison.
TEST(TypeOperatorElab, NonTypeRefLeftOfCompareRejected) {
  EXPECT_FALSE(
      ElabOk("module m #(parameter type T = int) ();\n"
             "  initial begin\n"
             "    if (7 == type(T)) $stop;\n"
             "  end\n"
             "endmodule\n"));
}

// §6.23 — the prohibition extends to the bang-equal form.
TEST(TypeOperatorElab, NonTypeRefBangEqRejected) {
  EXPECT_FALSE(
      ElabOk("module m #(parameter type T = int) ();\n"
             "  initial begin\n"
             "    if (type(T) !== 0) $stop;\n"
             "  end\n"
             "endmodule\n"));
}

// §6.23 — the inner expression of type(...) shall not contain a
// hierarchical reference. A member-access subtree is treated as a
// hierarchical reference here.
TEST(TypeOperatorElab, HierarchicalRefInTypeArgRejected) {
  EXPECT_FALSE(
      ElabOk("module sub;\n"
             "  int q;\n"
             "endmodule\n"
             "module m;\n"
             "  sub s();\n"
             "  var type(s.q) v;\n"
             "endmodule\n"));
}

// §6.23 — even when wrapped in a larger expression, a member-access
// subtree inside type(...) is rejected.
TEST(TypeOperatorElab, HierarchicalRefInBinaryArgRejected) {
  EXPECT_FALSE(
      ElabOk("module sub;\n"
             "  int q;\n"
             "endmodule\n"
             "module m;\n"
             "  sub s();\n"
             "  var type(s.q + 1) v;\n"
             "endmodule\n"));
}

// §6.23 — the inner expression of type(...) shall not reference an
// element of a dynamic object. A select whose base names a dynamic array
// is the smallest such reference.
TEST(TypeOperatorElab, DynamicArrayElementInTypeArgRejected) {
  EXPECT_FALSE(
      ElabOk("module m;\n"
             "  int d[];\n"
             "  var type(d[0]) v;\n"
             "endmodule\n"));
}

// §6.23 — an associative array is also a dynamic object; selecting an
// element of one inside type(...) is rejected.
TEST(TypeOperatorElab, AssocArrayElementInTypeArgRejected) {
  EXPECT_FALSE(
      ElabOk("module m;\n"
             "  int a[string];\n"
             "  var type(a[\"k\"]) v;\n"
             "endmodule\n"));
}

// §6.23 — a queue is a variable-size (dynamic) object as well, so selecting one
// of its elements inside type(...) is rejected, just like a dynamic or
// associative array element. This exercises the queue input form of the
// dynamic-object prohibition.
TEST(TypeOperatorElab, QueueElementInTypeArgRejected) {
  EXPECT_FALSE(
      ElabOk("module m;\n"
             "  int q[$];\n"
             "  var type(q[0]) v;\n"
             "endmodule\n"));
}

// §6.23 — a comparison of two type references is a constant expression, and the
// two references compare equal exactly when the referenced types match
// (§6.22.1) This is the accepting path for the `==` form: with `T` bound to
// `int`, the generate-if condition is true, so the then-block's declaration
// reaches the module and the else-block's does not. Observing which declaration
// survives shows the elaborator actually folding the comparison to true via
// type matching, not merely accepting the syntax.
TEST(TypeOperatorGenerate, EqualMatchingTypesSelectsThenBranch) {
  auto r = RunGenerateElaboration(
      "module top;\n"
      "  parameter type T = int;\n"
      "  if (type(T) == type(int)) begin\n"
      "    logic a;\n"
      "  end else begin\n"
      "    logic b;\n"
      "  end\n"
      "endmodule\n");
  ASSERT_NE(r.design, nullptr);
  EXPECT_FALSE(r.f.has_errors);
  ASSERT_EQ(r.design->top_modules.size(), 1u);
  EXPECT_EQ(CountVarsEndingWith(r.design->top_modules[0], 'a'), 1);
  EXPECT_EQ(CountVarsEndingWith(r.design->top_modules[0], 'b'), 0);
}

// §6.23 — the rejecting path for `==`: `int` and `real` are nonmatching types,
// so the condition folds to false and the else-block is the one instantiated.
TEST(TypeOperatorGenerate, EqualNonMatchingTypesSelectsElseBranch) {
  auto r = RunGenerateElaboration(
      "module top;\n"
      "  parameter type T = int;\n"
      "  if (type(T) == type(real)) begin\n"
      "    logic a;\n"
      "  end else begin\n"
      "    logic b;\n"
      "  end\n"
      "endmodule\n");
  ASSERT_NE(r.design, nullptr);
  EXPECT_FALSE(r.f.has_errors);
  ASSERT_EQ(r.design->top_modules.size(), 1u);
  EXPECT_EQ(CountVarsEndingWith(r.design->top_modules[0], 'a'), 0);
  EXPECT_EQ(CountVarsEndingWith(r.design->top_modules[0], 'b'), 1);
}

// §6.23 — the inequality form negates the match result: nonmatching types make
// `!=` true, selecting the then-block.
TEST(TypeOperatorGenerate, NotEqualNonMatchingTypesSelectsThenBranch) {
  auto r = RunGenerateElaboration(
      "module top;\n"
      "  parameter type T = int;\n"
      "  if (type(T) != type(real)) begin\n"
      "    logic a;\n"
      "  end else begin\n"
      "    logic b;\n"
      "  end\n"
      "endmodule\n");
  ASSERT_NE(r.design, nullptr);
  EXPECT_FALSE(r.f.has_errors);
  ASSERT_EQ(r.design->top_modules.size(), 1u);
  EXPECT_EQ(CountVarsEndingWith(r.design->top_modules[0], 'a'), 1);
  EXPECT_EQ(CountVarsEndingWith(r.design->top_modules[0], 'b'), 0);
}

// §6.23 — the case-equality operator behaves the same as equality for type
// references: matching types fold `===` to true, selecting the then-block.
TEST(TypeOperatorGenerate, CaseEqualMatchingTypesSelectsThenBranch) {
  auto r = RunGenerateElaboration(
      "module top;\n"
      "  parameter type T = int;\n"
      "  if (type(T) === type(int)) begin\n"
      "    logic a;\n"
      "  end else begin\n"
      "    logic b;\n"
      "  end\n"
      "endmodule\n");
  ASSERT_NE(r.design, nullptr);
  EXPECT_FALSE(r.f.has_errors);
  ASSERT_EQ(r.design->top_modules.size(), 1u);
  EXPECT_EQ(CountVarsEndingWith(r.design->top_modules[0], 'a'), 1);
  EXPECT_EQ(CountVarsEndingWith(r.design->top_modules[0], 'b'), 0);
}

// §6.23 — the case-inequality operator negates the match, so matching types
// fold `!==` to false and the else-block is instantiated.
TEST(TypeOperatorGenerate, CaseNotEqualMatchingTypesSelectsElseBranch) {
  auto r = RunGenerateElaboration(
      "module top;\n"
      "  parameter type T = int;\n"
      "  if (type(T) !== type(int)) begin\n"
      "    logic a;\n"
      "  end else begin\n"
      "    logic b;\n"
      "  end\n"
      "endmodule\n");
  ASSERT_NE(r.design, nullptr);
  EXPECT_FALSE(r.f.has_errors);
  ASSERT_EQ(r.design->top_modules.size(), 1u);
  EXPECT_EQ(CountVarsEndingWith(r.design->top_modules[0], 'a'), 0);
  EXPECT_EQ(CountVarsEndingWith(r.design->top_modules[0], 'b'), 1);
}

// §6.23 — both operands may be built-in data-type references rather than type
// parameters. `int` (signed) and `bit` (unsigned) are nonmatching, so the
// condition folds to false; the else-block is taken. This exercises the
// data-type (text) operand form of the fold, distinct from the type-parameter
// (identifier) form above.
TEST(TypeOperatorGenerate, BuiltinDataTypeReferencesFoldByMatching) {
  auto r = RunGenerateElaboration(
      "module top;\n"
      "  if (type(int) == type(bit)) begin\n"
      "    logic a;\n"
      "  end else begin\n"
      "    logic b;\n"
      "  end\n"
      "endmodule\n");
  ASSERT_NE(r.design, nullptr);
  EXPECT_FALSE(r.f.has_errors);
  ASSERT_EQ(r.design->top_modules.size(), 1u);
  EXPECT_EQ(CountVarsEndingWith(r.design->top_modules[0], 'a'), 0);
  EXPECT_EQ(CountVarsEndingWith(r.design->top_modules[0], 'b'), 1);
}

// §6.23 — the comparison being a constant expression must hold for each kind of
// constant type operand, which take different resolution paths. The parameter
// form is covered above; here the operand is a `localparam type`, and the
// generate-if still folds by type matching (localparam T bound to `int` matches
// `type(int)`), selecting the then-block.
TEST(TypeOperatorGenerate, LocalparamTypeOperandFoldsByMatching) {
  auto r = RunGenerateElaboration(
      "module top;\n"
      "  localparam type T = int;\n"
      "  if (type(T) == type(int)) begin\n"
      "    logic a;\n"
      "  end else begin\n"
      "    logic b;\n"
      "  end\n"
      "endmodule\n");
  ASSERT_NE(r.design, nullptr);
  EXPECT_FALSE(r.f.has_errors);
  ASSERT_EQ(r.design->top_modules.size(), 1u);
  EXPECT_EQ(CountVarsEndingWith(r.design->top_modules[0], 'a'), 1);
  EXPECT_EQ(CountVarsEndingWith(r.design->top_modules[0], 'b'), 0);
}

}  // namespace
