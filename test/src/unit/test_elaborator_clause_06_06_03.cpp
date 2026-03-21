#include "common/types.h"
#include "fixture_elaborator.h"

using namespace delta;

namespace {

TEST(WiredNetElaboration, WandNetType) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "module t;\n"
      "  wand w;\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.diag.HasErrors());

  auto* mod = design->top_modules[0];
  ASSERT_EQ(mod->nets.size(), 1u);
  EXPECT_EQ(mod->nets[0].net_type, NetType::kWand);
}

TEST(WiredNetElaboration, WorNetType) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "module t;\n"
      "  wor w;\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.diag.HasErrors());

  auto* mod = design->top_modules[0];
  ASSERT_EQ(mod->nets.size(), 1u);
  EXPECT_EQ(mod->nets[0].net_type, NetType::kWor);
}

TEST(WiredNetElaboration, TriandNetType) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "module t;\n"
      "  triand ta;\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.diag.HasErrors());

  auto* mod = design->top_modules[0];
  ASSERT_EQ(mod->nets.size(), 1u);
  EXPECT_EQ(mod->nets[0].net_type, NetType::kTriand);
}

TEST(WiredNetElaboration, TriorNetType) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "module t;\n"
      "  trior to1;\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.diag.HasErrors());

  auto* mod = design->top_modules[0];
  ASSERT_EQ(mod->nets.size(), 1u);
  EXPECT_EQ(mod->nets[0].net_type, NetType::kTrior);
}

TEST(WiredNetElaboration, WandAndTriandBothAreNets) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "module t;\n"
      "  wand a;\n"
      "  triand b;\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.diag.HasErrors());

  auto* mod = design->top_modules[0];
  ASSERT_EQ(mod->nets.size(), 2u);
  EXPECT_EQ(mod->nets[0].net_type, NetType::kWand);
  EXPECT_EQ(mod->nets[1].net_type, NetType::kTriand);
  EXPECT_TRUE(mod->variables.empty());
}

TEST(WiredNetElaboration, WorAndTriorBothAreNets) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "module t;\n"
      "  wor a;\n"
      "  trior b;\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.diag.HasErrors());

  auto* mod = design->top_modules[0];
  ASSERT_EQ(mod->nets.size(), 2u);
  EXPECT_EQ(mod->nets[0].net_type, NetType::kWor);
  EXPECT_EQ(mod->nets[1].net_type, NetType::kTrior);
  EXPECT_TRUE(mod->variables.empty());
}

}  // namespace
