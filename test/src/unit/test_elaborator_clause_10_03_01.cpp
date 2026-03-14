#include "fixture_elaborator.h"

using namespace delta;

namespace {

TEST(ContinuousAssignDeclElaboration, NetDeclAssign_CreatesContAssign) {
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

TEST(ContinuousAssignDeclElaboration, NetDeclAssign_LhsIsNetName) {
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

TEST(ContinuousAssignDeclElaboration, NetDeclAssign_Width) {
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

TEST(ContinuousAssignDeclElaboration, NetDeclAssign_DriveStrength) {
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

TEST(ContinuousAssignDeclElaboration, NetDeclNoInit_NoContAssign) {
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

TEST(ContinuousAssignDeclElaboration, InterconnectWithInit_Error) {
  ElabFixture f;
  Elaborate(
      "module t;\n"
      "  interconnect sig = 1;\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(f.has_errors);
}

TEST(ContinuousAssignDeclElaboration, InterconnectNoInit_Ok) {
  ElabFixture f;
  auto* design = Elaborate(
      "module t;\n"
      "  interconnect sig;\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
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

TEST(Elaborator, DriveStrengthOnNetDeclWithAssignIsValid) {
  ElabFixture f;
  auto* design = Elaborate(
      "module t;\n"
      "  wire (strong0, pull1) w = 1'b1;\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
}

}  // namespace
