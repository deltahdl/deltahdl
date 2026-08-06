

#include "elaborator/elaborator.h"
#include "elaborator/rtlir.h"
#include "fixture_elaborator.h"

using namespace delta;

namespace {

TEST(ScalarAndVectorDeclaration, ScalarWidth) {
  ElabFixture f;
  auto* design = Elaborate("module m; logic a; endmodule\n", f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
  auto* mod = design->top_modules[0];
  ASSERT_GE(mod->variables.size(), 1u);
  EXPECT_EQ(mod->variables[0].width, 1u);
}

TEST(ScalarAndVectorDeclaration, RegScalarWidth) {
  ElabFixture f;
  auto* design = Elaborate("module m; reg a; endmodule\n", f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
  auto* mod = design->top_modules[0];
  ASSERT_GE(mod->variables.size(), 1u);
  EXPECT_EQ(mod->variables[0].width, 1u);
}

TEST(ScalarAndVectorDeclaration, BitScalarWidth) {
  ElabFixture f;
  auto* design = Elaborate("module m; bit a; endmodule\n", f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
  auto* mod = design->top_modules[0];
  ASSERT_GE(mod->variables.size(), 1u);
  EXPECT_EQ(mod->variables[0].width, 1u);
}

TEST(ScalarAndVectorDeclaration, LogicTypedefScalarWidth) {
  ElabFixture f;
  auto* design = Elaborate(
      "module m;\n"
      "  typedef logic my_logic_t;\n"
      "  my_logic_t a;\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
  auto* mod = design->top_modules[0];
  ASSERT_GE(mod->variables.size(), 1u);
  EXPECT_EQ(mod->variables[0].width, 1u);
}

TEST(ScalarAndVectorDeclaration, ImplicitLogicScalarWidth) {
  ElabFixture f;
  auto* design = Elaborate(
      "module m;\n"
      "  var v;\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
  auto* mod = design->top_modules[0];
  ASSERT_GE(mod->variables.size(), 1u);
  EXPECT_EQ(mod->variables[0].width, 1u);
}

TEST(ScalarAndVectorDeclaration, MultibitRangeProducesVectorWidth) {
  ElabFixture f;
  auto* design = Elaborate("module m; logic [7:0] v; endmodule\n", f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
  auto* mod = design->top_modules[0];
  ASSERT_GE(mod->variables.size(), 1u);
  EXPECT_EQ(mod->variables[0].width, 8u);
}

TEST(ScalarAndVectorDeclaration, RegMultibitVectorWidth) {
  ElabFixture f;
  auto* design = Elaborate("module m; reg [3:0] r; endmodule\n", f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
  auto* mod = design->top_modules[0];
  ASSERT_GE(mod->variables.size(), 1u);
  EXPECT_EQ(mod->variables[0].width, 4u);
}

TEST(ScalarAndVectorDeclaration, BitMultibitVectorWidth) {
  ElabFixture f;
  auto* design = Elaborate("module m; bit [7:0] b; endmodule\n", f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
  auto* mod = design->top_modules[0];
  ASSERT_GE(mod->variables.size(), 1u);
  EXPECT_EQ(mod->variables[0].width, 8u);
}

TEST(ScalarAndVectorDeclaration, LogicTypedefVectorWidth) {
  ElabFixture f;
  auto* design = Elaborate(
      "module m;\n"
      "  typedef logic [7:0] byte_t;\n"
      "  byte_t b;\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
  auto* mod = design->top_modules[0];
  ASSERT_GE(mod->variables.size(), 1u);
  EXPECT_EQ(mod->variables[0].width, 8u);
}

TEST(ScalarAndVectorDeclaration, ImplicitLogicVectorWidth) {
  ElabFixture f;
  auto* design = Elaborate(
      "module m;\n"
      "  var [7:0] v;\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
  auto* mod = design->top_modules[0];
  ASSERT_GE(mod->variables.size(), 1u);
  EXPECT_EQ(mod->variables[0].width, 8u);
}

TEST(ScalarAndVectorDeclaration, BitTypedefScalarWidth) {
  ElabFixture f;
  auto* design = Elaborate(
      "module m;\n"
      "  typedef bit my_bit_t;\n"
      "  my_bit_t a;\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
  auto* mod = design->top_modules[0];
  ASSERT_GE(mod->variables.size(), 1u);
  EXPECT_EQ(mod->variables[0].width, 1u);
}

TEST(ScalarAndVectorDeclaration, RegTypedefScalarWidth) {
  ElabFixture f;
  auto* design = Elaborate(
      "module m;\n"
      "  typedef reg my_reg_t;\n"
      "  my_reg_t a;\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
  auto* mod = design->top_modules[0];
  ASSERT_GE(mod->variables.size(), 1u);
  EXPECT_EQ(mod->variables[0].width, 1u);
}

TEST(ScalarAndVectorDeclaration, BitTypedefVectorWidth) {
  ElabFixture f;
  auto* design = Elaborate(
      "module m;\n"
      "  typedef bit [3:0] nibble_t;\n"
      "  nibble_t b;\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
  auto* mod = design->top_modules[0];
  ASSERT_GE(mod->variables.size(), 1u);
  EXPECT_EQ(mod->variables[0].width, 4u);
}

TEST(ScalarAndVectorDeclaration, RegTypedefVectorWidth) {
  ElabFixture f;
  auto* design = Elaborate(
      "module m;\n"
      "  typedef reg [3:0] nibble_t;\n"
      "  nibble_t b;\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
  auto* mod = design->top_modules[0];
  ASSERT_GE(mod->variables.size(), 1u);
  EXPECT_EQ(mod->variables[0].width, 4u);
}

TEST(ScalarAndVectorDeclaration, MultipleScalarsHaveUnitWidth) {
  ElabFixture f;
  auto* design = Elaborate(
      "module m;\n"
      "  logic a, b, c;\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
  auto* mod = design->top_modules[0];
  ASSERT_GE(mod->variables.size(), 3u);
  EXPECT_EQ(mod->variables[0].width, 1u);
  EXPECT_EQ(mod->variables[1].width, 1u);
  EXPECT_EQ(mod->variables[2].width, 1u);
}

TEST(ScalarAndVectorDeclaration, MultipleVectorsHaveSpecifiedWidth) {
  ElabFixture f;
  auto* design = Elaborate(
      "module m;\n"
      "  logic [3:0] a, b, c;\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
  auto* mod = design->top_modules[0];
  ASSERT_GE(mod->variables.size(), 3u);
  EXPECT_EQ(mod->variables[0].width, 4u);
  EXPECT_EQ(mod->variables[1].width, 4u);
  EXPECT_EQ(mod->variables[2].width, 4u);
}

}  // namespace
