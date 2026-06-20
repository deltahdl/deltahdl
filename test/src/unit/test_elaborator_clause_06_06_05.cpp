#include "common/types.h"
#include "fixture_elaborator.h"

using namespace delta;

namespace {

TEST(Tri0Tri1Elaboration, Tri0NetType) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "module t;\n"
      "  tri0 t0;\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.diag.HasErrors());

  auto* mod = design->top_modules[0];
  ASSERT_EQ(mod->nets.size(), 1u);
  EXPECT_EQ(mod->nets[0].net_type, NetType::kTri0);
}

TEST(Tri0Tri1Elaboration, Tri1NetType) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "module t;\n"
      "  tri1 t1;\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.diag.HasErrors());

  auto* mod = design->top_modules[0];
  ASSERT_EQ(mod->nets.size(), 1u);
  EXPECT_EQ(mod->nets[0].net_type, NetType::kTri1);
}

TEST(Tri0Tri1Elaboration, Tri0IsNetNotVariable) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "module t;\n"
      "  tri0 t0;\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.diag.HasErrors());

  auto* mod = design->top_modules[0];
  EXPECT_EQ(mod->nets.size(), 1u);
  EXPECT_TRUE(mod->variables.empty());
}

TEST(Tri0Tri1Elaboration, Tri1IsNetNotVariable) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "module t;\n"
      "  tri1 t1;\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.diag.HasErrors());

  auto* mod = design->top_modules[0];
  EXPECT_EQ(mod->nets.size(), 1u);
  EXPECT_TRUE(mod->variables.empty());
}

}  // namespace
