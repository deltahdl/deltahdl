

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

// §6.9: A matching user-defined type without a range is a 1-bit scalar.
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

// §6.9: An object declared implicitly as logic without a range is a 1-bit
// scalar.
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

// §6.9: Each variable in a multi-name declaration without a range is its
// own 1-bit scalar.
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

}  // namespace
