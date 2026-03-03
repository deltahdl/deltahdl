// Non-LRM tests

#include "fixture_simulator.h"
#include "simulator/lowerer.h"
#include "simulator/variable.h"

using namespace delta;

namespace {

// 24. type() with longint, assign max value.
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

// 25. type() with shortint, assign zero.
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

// 26. type() with byte preserves signedness in arithmetic context.
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
  // 100 + 55 = 155.
  EXPECT_EQ(var->value.ToUint64(), 155u);
}

// 27. type() with int, chained: type(a) b, type(b) c.
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

// 28. type() with int, value preserved after multiple assignments.
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

// 29. type() with shortint, assign max unsigned 16-bit value.
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

// 30. type() from byte, assigned via expression from wider variable.
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
  // 0x12345678 truncated to 8 bits = 0x78.
  EXPECT_EQ(var->value.ToUint64(), 0x78u);
  EXPECT_TRUE(var->is_signed);
}

}  // namespace
