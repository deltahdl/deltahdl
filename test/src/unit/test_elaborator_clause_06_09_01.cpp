

#include "elaborator/elaborator.h"
#include "elaborator/rtlir.h"
#include "fixture_elaborator.h"

using namespace delta;

namespace {

TEST(ElabSection6, Sec6_9_1_LittleEndianWidth) {
  ElabFixture f;
  auto* design = Elaborate("module m; logic [0:7] x; endmodule\n", f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
  auto* mod = design->top_modules[0];
  ASSERT_GE(mod->variables.size(), 1u);
  EXPECT_EQ(mod->variables[0].width, 8u);
}

TEST(ElabSection6, Sec6_9_1_32BitVectorWidth) {
  ElabFixture f;
  auto* design = Elaborate("module m; logic [31:0] w; endmodule\n", f);
  ASSERT_NE(design, nullptr);
  auto* mod = design->top_modules[0];
  ASSERT_GE(mod->variables.size(), 1u);
  EXPECT_EQ(mod->variables[0].width, 32u);
}

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

TEST(ElabSection6, Sec6_9_1_VectorDefaultUnsigned) {
  ElabFixture f;
  auto* design = Elaborate("module m; logic [7:0] data; endmodule\n", f);
  ASSERT_NE(design, nullptr);
  auto* mod = design->top_modules[0];
  ASSERT_GE(mod->variables.size(), 1u);
  EXPECT_FALSE(mod->variables[0].is_signed);
}

TEST(ElabSection6, Sec6_9_1_ExplicitlySigned) {
  ElabFixture f;
  auto* design = Elaborate("module m; logic signed [7:0] sv; endmodule\n", f);
  ASSERT_NE(design, nullptr);
  auto* mod = design->top_modules[0];
  ASSERT_GE(mod->variables.size(), 1u);
  EXPECT_TRUE(mod->variables[0].is_signed);
}

}
