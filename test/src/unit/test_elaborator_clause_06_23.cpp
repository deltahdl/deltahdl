#include "fixture_simulator.h"
#include "simulator/lowerer.h"
#include "simulator/variable.h"

using namespace delta;

namespace {

TEST(SimCh6, TypeRefVarDecl) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "module t;\n"
      "  int a;\n"
      "  var type(a) b;\n"
      "  initial begin\n"
      "    a = 42;\n"
      "    b = 100;\n"
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
  EXPECT_EQ(var->value.ToUint64(), 100u);
}

TEST(SimCh6b, TypeOpInt) {
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

TEST(SimCh6b, TypeOpLogic) {
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

TEST(SimCh6b, TypeOpByte) {
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

TEST(SimCh6b, TypeOpShortint) {
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

TEST(SimCh6b, TypeOpLongint) {
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

TEST(SimCh6b, TypeOpInteger) {
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

TEST(SimCh6b, TypeOpReal) {
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

TEST(SimCh6b, TypeOpPreservesSignedInt) {
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

TEST(SimCh6b, TypeOpPreservesUnsignedLogic) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "module t;\n"
      "  logic a;\n"
      "  var type(a) result;\n"
      "  initial result = 1;\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);

  Lowerer lowerer(f.ctx, f.arena, f.diag);
  lowerer.Lower(design);
  f.scheduler.Run();

  auto* var = f.ctx.FindVariable("result");
  ASSERT_NE(var, nullptr);
  EXPECT_FALSE(var->is_signed);
  EXPECT_EQ(var->value.ToUint64(), 1u);
}

TEST(SimCh6b, TypeOpShortintWidth16) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "module t;\n"
      "  shortint a;\n"
      "  var type(a) result;\n"
      "  initial result = 16'hCAFE;\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);

  Lowerer lowerer(f.ctx, f.arena, f.diag);
  lowerer.Lower(design);
  f.scheduler.Run();

  auto* var = f.ctx.FindVariable("result");
  ASSERT_NE(var, nullptr);
  EXPECT_EQ(var->value.width, 16u);
  EXPECT_EQ(var->value.ToUint64(), 0xCAFEu);
}

TEST(SimCh6b, TypeOpIntegerWidth32) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "module t;\n"
      "  integer a;\n"
      "  var type(a) result;\n"
      "  initial result = 32'hDEADBEEF;\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);

  Lowerer lowerer(f.ctx, f.arena, f.diag);
  lowerer.Lower(design);
  f.scheduler.Run();

  auto* var = f.ctx.FindVariable("result");
  ASSERT_NE(var, nullptr);
  EXPECT_EQ(var->value.width, 32u);
  EXPECT_EQ(var->value.ToUint64(), 0xDEADBEEFu);
}

TEST(SimCh6b, TypeOpWidthTruncation) {
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

TEST(SimCh6b, TypeOpIntDifferentValues) {
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

TEST(SimCh6b, TypeOpShortintSignExtension) {
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

TEST(SimCh6b, TypeOpParameterTypeDefault) {
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

TEST(SimCh6b, TypeOpEnumType) {
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

TEST(SimCh6b, TypeOpByteComputation) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "module t;\n"
      "  byte a;\n"
      "  var type(a) result;\n"
      "  initial begin\n"
      "    a = 100;\n"
      "    result = a + 50;\n"
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

  EXPECT_EQ(var->value.ToUint64(), 150u);
}

TEST(SimCh6b, TypeOpIntOverflow) {
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

TEST(SimCh6b, TypeOpMatchingWidths) {
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

TEST(SimCh6b, TypeOpByteFullRange) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "module t;\n"
      "  byte a;\n"
      "  var type(a) result;\n"
      "  initial result = 8'hFF;\n"
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

TEST(SimCh6b, TypeOpLongintFullValue) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "module t;\n"
      "  longint a;\n"
      "  var type(a) result;\n"
      "  initial result = 64'hCAFEBABE_DEADBEEF;\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);

  Lowerer lowerer(f.ctx, f.arena, f.diag);
  lowerer.Lower(design);
  f.scheduler.Run();

  auto* var = f.ctx.FindVariable("result");
  ASSERT_NE(var, nullptr);
  EXPECT_EQ(var->value.width, 64u);
  EXPECT_EQ(var->value.ToUint64(), 0xCAFEBABEDEADBEEFu);
}

TEST(SimCh6b, TypeOpLongintMaxValue) {
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

TEST(SimCh6b, TypeOpShortintZero) {
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

TEST(SimCh6b, TypeOpByteArithmeticSigned) {
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

TEST(SimCh6b, TypeOpChainedTypeRef) {
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

TEST(SimCh6b, TypeOpMultipleAssignments) {
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

TEST(SimCh6b, TypeOpShortintMaxUnsigned) {
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

TEST(SimCh6b, TypeOpByteFromWiderAssignment) {
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

TEST(SimCh6b, TypeOpLocalparamType) {
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

TEST(SimCh6b, TypeOpLogicVector) {
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

}  // namespace
