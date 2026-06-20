#include "common/types.h"
#include "fixture_elaborator.h"

using namespace delta;

namespace {

TEST(SupplyNetElaboration, Supply0NetType) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "module t;\n"
      "  supply0 gnd;\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.diag.HasErrors());

  auto* mod = design->top_modules[0];
  ASSERT_EQ(mod->nets.size(), 1u);
  EXPECT_EQ(mod->nets[0].net_type, NetType::kSupply0);
}

TEST(SupplyNetElaboration, Supply1NetType) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "module t;\n"
      "  supply1 vdd;\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.diag.HasErrors());

  auto* mod = design->top_modules[0];
  ASSERT_EQ(mod->nets.size(), 1u);
  EXPECT_EQ(mod->nets[0].net_type, NetType::kSupply1);
}

TEST(SupplyNetElaboration, Supply0IsNetNotVariable) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "module t;\n"
      "  supply0 gnd;\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.diag.HasErrors());

  auto* mod = design->top_modules[0];
  EXPECT_EQ(mod->nets.size(), 1u);
  EXPECT_TRUE(mod->variables.empty());
}

TEST(SupplyNetElaboration, Supply1IsNetNotVariable) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "module t;\n"
      "  supply1 vdd;\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.diag.HasErrors());

  auto* mod = design->top_modules[0];
  EXPECT_EQ(mod->nets.size(), 1u);
  EXPECT_TRUE(mod->variables.empty());
}

}  // namespace
