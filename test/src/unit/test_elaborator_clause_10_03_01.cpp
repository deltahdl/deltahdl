#include "fixture_elaborator.h"

using namespace delta;

namespace {

TEST(ContinuousAssignDeclElaboration, NetDeclAssignCreatesContAssign) {
  ElabFixture f;
  auto* design = Elaborate(
      "module t;\n"
      "  wire w = 1'b1;\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
  auto* mod = design->top_modules[0];
  ASSERT_EQ(mod->nets.size(), 1u);
  EXPECT_EQ(mod->nets[0].name, "w");
  ASSERT_GE(mod->assigns.size(), 1u);
  EXPECT_NE(mod->assigns[0].lhs, nullptr);
  EXPECT_NE(mod->assigns[0].rhs, nullptr);
}

TEST(ContinuousAssignDeclElaboration, NetDeclAssignLhsIsNetName) {
  ElabFixture f;
  auto* design = Elaborate(
      "module t;\n"
      "  wire mynet = 1'b0;\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
  auto* mod = design->top_modules[0];
  ASSERT_GE(mod->assigns.size(), 1u);
  auto& ca = mod->assigns[0];
  ASSERT_NE(ca.lhs, nullptr);
  EXPECT_EQ(ca.lhs->kind, ExprKind::kIdentifier);
  EXPECT_EQ(ca.lhs->text, "mynet");
}

TEST(ContinuousAssignDeclElaboration, NetDeclAssignWidth) {
  ElabFixture f;
  auto* design = Elaborate(
      "module t;\n"
      "  wire [7:0] data = 8'hAB;\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
  auto* mod = design->top_modules[0];
  ASSERT_GE(mod->assigns.size(), 1u);
  EXPECT_EQ(mod->assigns[0].width, 8u);
}

TEST(ContinuousAssignDeclElaboration, NetDeclAssignDriveStrength) {
  ElabFixture f;
  auto* design = Elaborate(
      "module t;\n"
      "  wire (strong1, pull0) w = 1'b1;\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
  auto* mod = design->top_modules[0];
  ASSERT_GE(mod->assigns.size(), 1u);
  EXPECT_NE(mod->assigns[0].drive_strength0, 0);
  EXPECT_NE(mod->assigns[0].drive_strength1, 0);
}

TEST(ContinuousAssignDeclElaboration, NetDeclNoInitNoContAssign) {
  ElabFixture f;
  auto* design = Elaborate(
      "module t;\n"
      "  wire w;\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
  auto* mod = design->top_modules[0];
  EXPECT_EQ(mod->assigns.size(), 0u);
}

TEST(ContinuousAssignDeclElaboration, MultiNetDeclAssign) {
  ElabFixture f;
  auto* design = Elaborate(
      "module t;\n"
      "  wire a = 1'b0, b = 1'b1;\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
  auto* mod = design->top_modules[0];
  ASSERT_GE(mod->assigns.size(), 2u);
}

TEST(ContinuousAssignDeclElaboration, NetDeclAssignConflictsWithProcAssign) {
  ElabFixture f;
  Elaborate(
      "module t;\n"
      "  wire w = 1'b0;\n"
      "  initial w = 1'b1;\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(f.has_errors);
}

TEST(ContinuousAssignDeclElaboration, InterconnectNetDeclAssignIsError) {
  ElabFixture f;
  Elaborate(
      "module t;\n"
      "  interconnect sig = 1;\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(f.has_errors);
}

TEST(ContinuousAssignDeclElaboration, TriNetDeclAssignCreatesContAssign) {
  ElabFixture f;
  auto* design = Elaborate(
      "module t;\n"
      "  tri w = 1'b0;\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
  auto* mod = design->top_modules[0];
  ASSERT_GE(mod->assigns.size(), 1u);
  EXPECT_NE(mod->assigns[0].lhs, nullptr);
  EXPECT_NE(mod->assigns[0].rhs, nullptr);
}

TEST(ContinuousAssignDeclElaboration, InterconnectVectorNetDeclAssignIsError) {
  ElabFixture f;
  Elaborate(
      "module t;\n"
      "  interconnect [3:0] bus = 4'b0;\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(f.has_errors);
}

}  // namespace
