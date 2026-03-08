#include "fixture_simulator.h"
#include "simulator/lowerer.h"
#include "simulator/variable.h"

using namespace delta;

namespace {

// §11.10.1: Copy — assign string literal to a bit vector.
TEST(SimA11101, StringLiteralCopyToVector) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "module t;\n"
      "  bit [8*5:1] s;\n"
      "  initial s = \"Hello\";\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  Lowerer lowerer(f.ctx, f.arena, f.diag);
  lowerer.Lower(design);
  f.scheduler.Run();
  auto* var = f.ctx.FindVariable("s");
  ASSERT_NE(var, nullptr);
  // "Hello" = 0x48656c6c6f
  EXPECT_EQ(var->value.ToUint64(), 0x48656c6c6fULL);
}

// §11.10.1: Copy — string assigned to wider vector is left-padded with zeros.
TEST(SimA11101, StringLiteralCopyPaddedWithZeros) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "module t;\n"
      "  bit [8*8:1] s;\n"
      "  initial s = \"Hi\";\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  Lowerer lowerer(f.ctx, f.arena, f.diag);
  lowerer.Lower(design);
  f.scheduler.Run();
  auto* var = f.ctx.FindVariable("s");
  ASSERT_NE(var, nullptr);
  // "Hi" = 0x4869, zero-padded in 64-bit vector.
  EXPECT_EQ(var->value.ToUint64(), 0x4869ULL);
}

// §11.10.1: Concatenate — concatenation of string-valued vectors.
TEST(SimA11101, StringLiteralConcatenate) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "module t;\n"
      "  bit [8*14:1] stringvar;\n"
      "  initial begin\n"
      "    stringvar = \"Hello world\";\n"
      "    stringvar = {stringvar, \"!!!\"};\n"
      "  end\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  Lowerer lowerer(f.ctx, f.arena, f.diag);
  lowerer.Lower(design);
  f.scheduler.Run();
  auto* var = f.ctx.FindVariable("stringvar");
  ASSERT_NE(var, nullptr);
  // After concat and truncation to 14*8=112 bits:
  // "Hello world" is 11 chars, "!!!" is 3 chars = 14 chars total.
  // "Hello world!!!" = 0x48656c6c6f20776f726c64212121
  // Check last byte is '!' = 0x21.
  EXPECT_EQ(var->value.words[0].aval & 0xFF, 0x21u);
}

// §11.10.1: Compare — equality of string literal values in vectors.
TEST(SimA11101, StringLiteralCompareEqual) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "module t;\n"
      "  bit [8*5:1] s1, s2;\n"
      "  logic result;\n"
      "  initial begin\n"
      "    s1 = \"Hello\";\n"
      "    s2 = \"Hello\";\n"
      "    result = (s1 == s2);\n"
      "  end\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  Lowerer lowerer(f.ctx, f.arena, f.diag);
  lowerer.Lower(design);
  f.scheduler.Run();
  auto* var = f.ctx.FindVariable("result");
  ASSERT_NE(var, nullptr);
  EXPECT_EQ(var->value.ToUint64(), 1u);
}

// §11.10.1: Compare — inequality of different string literal values.
TEST(SimA11101, StringLiteralCompareNotEqual) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "module t;\n"
      "  bit [8*5:1] s1, s2;\n"
      "  logic result;\n"
      "  initial begin\n"
      "    s1 = \"Hello\";\n"
      "    s2 = \"World\";\n"
      "    result = (s1 != s2);\n"
      "  end\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  Lowerer lowerer(f.ctx, f.arena, f.diag);
  lowerer.Lower(design);
  f.scheduler.Run();
  auto* var = f.ctx.FindVariable("result");
  ASSERT_NE(var, nullptr);
  EXPECT_EQ(var->value.ToUint64(), 1u);
}

// §11.10.1: Single-character string literal.
TEST(SimA11101, SingleCharStringLiteral) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "module t;\n"
      "  bit [7:0] ch;\n"
      "  initial ch = \"A\";\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  Lowerer lowerer(f.ctx, f.arena, f.diag);
  lowerer.Lower(design);
  f.scheduler.Run();
  auto* var = f.ctx.FindVariable("ch");
  ASSERT_NE(var, nullptr);
  EXPECT_EQ(var->value.ToUint64(), 0x41u);
}

}  // namespace
