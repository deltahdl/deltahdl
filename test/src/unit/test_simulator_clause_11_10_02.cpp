#include "fixture_simulator.h"
#include "simulator/lowerer.h"
#include "simulator/variable.h"

using namespace delta;

namespace {

// §11.10.2: String assigned to wider vector is left-padded with zeros.
TEST(SimA11102, StringLiteralPaddedWithZeros) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "module t;\n"
      "  bit [8*10:1] s;\n"
      "  initial s = \"Hello\";\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  Lowerer lowerer(f.ctx, f.arena, f.diag);
  lowerer.Lower(design);
  f.scheduler.Run();
  auto* var = f.ctx.FindVariable("s");
  ASSERT_NE(var, nullptr);
  // "Hello" is 5 bytes = 0x48656c6c6f, in 80-bit vector → upper 40 bits are 0.
  EXPECT_EQ(var->value.words[0].aval, 0x00000048656c6c6fULL);
  EXPECT_EQ(var->value.words[1].aval & 0xFFFF, 0x0000u);
}

// §11.10.2: Padding causes concatenation of padded vectors to differ from
// the concatenation of the original string literal.
TEST(SimA11102, PaddingAffectsConcatComparison) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "module t;\n"
      "  bit [8*10:1] s1, s2;\n"
      "  logic result;\n"
      "  initial begin\n"
      "    s1 = \"Hello\";\n"
      "    s2 = \" world!\";\n"
      "    result = ({s1, s2} == \"Hello world!\");\n"
      "  end\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  Lowerer lowerer(f.ctx, f.arena, f.diag);
  lowerer.Lower(design);
  f.scheduler.Run();
  auto* var = f.ctx.FindVariable("result");
  ASSERT_NE(var, nullptr);
  // §11.10.2: The comparison fails because s1 and s2 contain zero padding.
  EXPECT_EQ(var->value.ToUint64(), 0u);
}

// §11.10.2: When vector width exactly matches string length, no padding occurs.
TEST(SimA11102, ExactWidthNoPadding) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "module t;\n"
      "  bit [8*5:1] s1;\n"
      "  bit [8*7:1] s2;\n"
      "  bit [8*12:1] combined;\n"
      "  logic result;\n"
      "  initial begin\n"
      "    s1 = \"Hello\";\n"
      "    s2 = \" world!\";\n"
      "    combined = {s1, s2};\n"
      "    result = (combined == \"Hello world!\");\n"
      "  end\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  Lowerer lowerer(f.ctx, f.arena, f.diag);
  lowerer.Lower(design);
  f.scheduler.Run();
  auto* var = f.ctx.FindVariable("result");
  ASSERT_NE(var, nullptr);
  // With exact-width vectors, no padding → concatenation matches the literal.
  EXPECT_EQ(var->value.ToUint64(), 1u);
}

// §11.10.2: Padding zeros are indistinguishable from NUL characters.
TEST(SimA11102, PaddingIndistinguishableFromNul) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "module t;\n"
      "  bit [8*3:1] s;\n"
      "  logic result;\n"
      "  initial begin\n"
      "    s = \"A\";\n"
      "    result = (s == {8'd0, 8'd0, 8'd65});\n"
      "  end\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  Lowerer lowerer(f.ctx, f.arena, f.diag);
  lowerer.Lower(design);
  f.scheduler.Run();
  auto* var = f.ctx.FindVariable("result");
  ASSERT_NE(var, nullptr);
  // Padding zeros match explicit zero bytes — they are indistinguishable.
  EXPECT_EQ(var->value.ToUint64(), 1u);
}

// §11.10.2: Self-comparison of a padded string succeeds.
TEST(SimA11102, PaddedStringSelfCompare) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "module t;\n"
      "  bit [8*10:1] s;\n"
      "  logic result;\n"
      "  initial begin\n"
      "    s = \"test\";\n"
      "    result = (s == s);\n"
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

}  // namespace
