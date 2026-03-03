// §6.23: Type operator

#include "fixture_simulator.h"
#include "simulator/lowerer.h"
#include "simulator/variable.h"

using namespace delta;

namespace {

// §6.23: type(expr) in variable declaration resolves type.
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
  // type(a) = int → 32-bit width
  EXPECT_EQ(var->value.width, 32u);
  EXPECT_EQ(var->value.ToUint64(), 100u);
}

// --------------------------------------------------------------------------
// §6.11.1: type(expression) used in `var type(expr) name;` declarations.
// The type operator resolves to the same type, width, and signedness as
// the referenced expression.
// --------------------------------------------------------------------------
// 1. type() with int: resolves to 32-bit signed.
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

// 2. type() with logic: resolves to 1-bit unsigned.
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

// 3. type() with byte: resolves to 8-bit signed.
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

// 4. type() with shortint: resolves to 16-bit signed.
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

// 5. type() with longint: resolves to 64-bit signed.
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

}  // namespace
