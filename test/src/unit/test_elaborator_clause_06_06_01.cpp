#include "common/types.h"
#include "fixture_elaborator.h"

using namespace delta;

namespace {

TEST(Elaboration, WireNetType) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "module t;\n"
      "  wire w;\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.diag.HasErrors());

  ASSERT_FALSE(design->top_modules.empty());
  auto* mod = design->top_modules[0];
  ASSERT_EQ(mod->nets.size(), 1u);
  EXPECT_EQ(mod->nets[0].name, "w");
  EXPECT_EQ(mod->nets[0].net_type, NetType::kWire);
}

TEST(Elaboration, TriNetType) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "module t;\n"
      "  tri n;\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.diag.HasErrors());

  ASSERT_FALSE(design->top_modules.empty());
  auto* mod = design->top_modules[0];
  ASSERT_EQ(mod->nets.size(), 1u);
  EXPECT_EQ(mod->nets[0].name, "n");
  EXPECT_EQ(mod->nets[0].net_type, NetType::kTri);
}

TEST(Elaboration, WireAndTriAreNets) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "module t;\n"
      "  wire a;\n"
      "  tri b;\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.diag.HasErrors());

  auto* mod = design->top_modules[0];
  ASSERT_EQ(mod->nets.size(), 2u);
  EXPECT_EQ(mod->nets[0].net_type, NetType::kWire);
  EXPECT_EQ(mod->nets[1].net_type, NetType::kTri);
  EXPECT_TRUE(mod->variables.empty());
}

TEST(Elaboration, WireVectorWidth) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "module t;\n"
      "  wire [7:0] bus;\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.diag.HasErrors());

  auto* mod = design->top_modules[0];
  ASSERT_EQ(mod->nets.size(), 1u);
  EXPECT_EQ(mod->nets[0].width, 8u);
  EXPECT_EQ(mod->nets[0].net_type, NetType::kWire);
}

TEST(Elaboration, TriVectorWidth) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "module t;\n"
      "  tri [15:0] bus;\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.diag.HasErrors());

  auto* mod = design->top_modules[0];
  ASSERT_EQ(mod->nets.size(), 1u);
  EXPECT_EQ(mod->nets[0].width, 16u);
  EXPECT_EQ(mod->nets[0].net_type, NetType::kTri);
}

TEST(Elaboration, WireRedeclarationError) {
  ElabFixture f;
  ElaborateSrc(
      "module t;\n"
      "  wire w;\n"
      "  wire w;\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(f.diag.HasErrors());
}

}
