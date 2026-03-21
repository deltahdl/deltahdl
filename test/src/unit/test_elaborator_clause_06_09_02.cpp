

#include <gtest/gtest.h>

#include "fixture_elaborator.h"
#include "model_net_declaration.h"

using namespace delta;

namespace {

TEST(VectorNetAccessibility, VectoredNetElaboratesOk) {
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

TEST(VectorNetAccessibility, ScalaredNetElaboratesOk) {
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

TEST(VectorNetAccessibility, VectoredWithPackedDimOk) {
  NetDeclInfo info;
  info.is_vectored = true;
  info.packed_dim_count = 1;
  EXPECT_TRUE(ValidateNetDecl(info));
}

TEST(VectorNetAccessibility, ScalaredWithPackedDimOk) {
  NetDeclInfo info;
  info.is_scalared = true;
  info.packed_dim_count = 1;
  EXPECT_TRUE(ValidateNetDecl(info));
}

TEST(VectorNetAccessibility, VectoredWithPackedDimElabOk) {
  EXPECT_TRUE(
      ElabOk("module m;\n"
             "  wire vectored [7:0] bus;\n"
             "endmodule\n"));
}

TEST(VectorNetAccessibility, ScalaredWithPackedDimElabOk) {
  EXPECT_TRUE(
      ElabOk("module m;\n"
             "  wire scalared [3:0] w;\n"
             "endmodule\n"));
}

TEST(VectorNetAccessibility, VectoredWithoutPackedDimIsError) {
  ElabFixture f;
  ElaborateSrc(
      "module m;\n"
      "  wire vectored w;\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(f.has_errors);
}

TEST(VectorNetAccessibility, ScalaredWithoutPackedDimIsError) {
  ElabFixture f;
  ElaborateSrc(
      "module m;\n"
      "  wire scalared w;\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(f.has_errors);
}

}  // namespace
