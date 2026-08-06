#include "common/types.h"
#include "fixture_elaborator.h"

using namespace delta;

namespace {

TEST(WireTriElaboration, WireNetType) {
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

TEST(WireTriElaboration, TriNetType) {
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

TEST(WireTriElaboration, WireAndTriAreNets) {
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

TEST(WireTriElaboration, WireVectorWidth) {
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

TEST(WireTriElaboration, TriVectorWidth) {
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

TEST(WireTriElaboration, WireMultipleDeclarators) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "module t;\n"
      "  wire a, b, c;\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.diag.HasErrors());

  auto* mod = design->top_modules[0];
  ASSERT_EQ(mod->nets.size(), 3u);
  EXPECT_EQ(mod->nets[0].net_type, NetType::kWire);
  EXPECT_EQ(mod->nets[1].net_type, NetType::kWire);
  EXPECT_EQ(mod->nets[2].net_type, NetType::kWire);
}

TEST(WireTriElaboration, TriMultipleDeclarators) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "module t;\n"
      "  tri a, b, c;\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.diag.HasErrors());

  auto* mod = design->top_modules[0];
  ASSERT_EQ(mod->nets.size(), 3u);
  EXPECT_EQ(mod->nets[0].net_type, NetType::kTri);
  EXPECT_EQ(mod->nets[1].net_type, NetType::kTri);
  EXPECT_EQ(mod->nets[2].net_type, NetType::kTri);
}

}  // namespace
