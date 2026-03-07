#include <gtest/gtest.h>

#include "fixture_elaborator.h"
#include "model_net_declaration.h"

using namespace delta;

namespace {

TEST(NetDecl, VectoredWithPackedDimensionOk) {
  NetDeclInfo info;
  info.is_vectored = true;
  info.packed_dim_count = 1;
  EXPECT_TRUE(ValidateNetDecl(info));
}

TEST(NetDecl, ScalaredWithPackedDimensionOk) {
  NetDeclInfo info;
  info.is_scalared = true;
  info.packed_dim_count = 1;
  EXPECT_TRUE(ValidateNetDecl(info));
}

// §6.9.2: Vectored net elaborates without error.
TEST(NetDecl, VectoredNetElaboratesOk) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "module t;\n"
      "  wire vectored [31:0] data;\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
  auto* mod = design->top_modules[0];
  ASSERT_GE(mod->nets.size(), 1u);
  EXPECT_EQ(mod->nets[0].width, 32u);
}

// §6.9.2: Scalared net elaborates without error.
TEST(NetDecl, ScalaredNetElaboratesOk) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "module t;\n"
      "  tri1 scalared [63:0] bus64;\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
  auto* mod = design->top_modules[0];
  ASSERT_GE(mod->nets.size(), 1u);
  EXPECT_EQ(mod->nets[0].width, 64u);
}

}  // namespace
