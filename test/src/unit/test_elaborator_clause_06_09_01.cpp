#include "elaborator/elaborator.h"
#include "elaborator/rtlir.h"
#include "fixture_elaborator.h"

using namespace delta;

namespace {

TEST(ParserA25, PackedDimElaboratesWidth) {
  ElabFixture f;
  auto* design = Elaborate("module m; logic [7:0] x; endmodule\n", f);
  ASSERT_NE(design, nullptr);
  auto* mod = design->top_modules[0];
  ASSERT_GE(mod->variables.size(), 1u);
  EXPECT_EQ(mod->variables[0].name, "x");
  EXPECT_EQ(mod->variables[0].width, 8u);
}

TEST(ElabA83, GenvarExprElaborates) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "module m;\n"
      "  parameter int N = 4;\n"
      "  logic [N-1:0] w;\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
}

// §6.9.1: Little-endian range [0:7] has width 8.
TEST(ElabSection6, Sec6_9_1_LittleEndianWidth) {
  ElabFixture f;
  auto* design = Elaborate("module m; logic [0:7] x; endmodule\n", f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
  auto* mod = design->top_modules[0];
  ASSERT_GE(mod->variables.size(), 1u);
  EXPECT_EQ(mod->variables[0].width, 8u);
}

// §6.9.1: Scalar (no range) has width 1.
TEST(ElabSection6, Sec6_9_1_ScalarWidth) {
  ElabFixture f;
  auto* design = Elaborate("module m; logic a; endmodule\n", f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
  auto* mod = design->top_modules[0];
  ASSERT_GE(mod->variables.size(), 1u);
  EXPECT_EQ(mod->variables[0].width, 1u);
}

// §6.9.1: 32-bit vector width.
TEST(ElabSection6, Sec6_9_1_32BitVectorWidth) {
  ElabFixture f;
  auto* design = Elaborate("module m; logic [31:0] w; endmodule\n", f);
  ASSERT_NE(design, nullptr);
  auto* mod = design->top_modules[0];
  ASSERT_GE(mod->variables.size(), 1u);
  EXPECT_EQ(mod->variables[0].width, 32u);
}

// §6.9.1: Net vector width matches variable vector width.
TEST(ElabSection6, Sec6_9_1_NetAndVarSameWidth) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "module m;\n"
      "  wire [15:0] net_w;\n"
      "  logic [15:0] var_v;\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
  auto* mod = design->top_modules[0];
  ASSERT_GE(mod->nets.size(), 1u);
  ASSERT_GE(mod->variables.size(), 1u);
  EXPECT_EQ(mod->nets[0].width, 16u);
  EXPECT_EQ(mod->variables[0].width, 16u);
}

// §6.9.1: Vectors of logic/reg/bit default to unsigned.
TEST(ElabSection6, Sec6_9_1_VectorDefaultUnsigned) {
  ElabFixture f;
  auto* design = Elaborate("module m; logic [7:0] data; endmodule\n", f);
  ASSERT_NE(design, nullptr);
  auto* mod = design->top_modules[0];
  ASSERT_GE(mod->variables.size(), 1u);
  EXPECT_FALSE(mod->variables[0].is_signed);
}

// §6.9.1: Explicitly signed vector.
TEST(ElabSection6, Sec6_9_1_ExplicitlySigned) {
  ElabFixture f;
  auto* design =
      Elaborate("module m; logic signed [7:0] sv; endmodule\n", f);
  ASSERT_NE(design, nullptr);
  auto* mod = design->top_modules[0];
  ASSERT_GE(mod->variables.size(), 1u);
  EXPECT_TRUE(mod->variables[0].is_signed);
}

}  // namespace
