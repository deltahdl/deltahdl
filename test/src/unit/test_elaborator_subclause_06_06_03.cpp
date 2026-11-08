#include <gtest/gtest.h>

#include "common/types.h"
#include "fixture_elaborator.h"

using namespace delta;

namespace {

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
