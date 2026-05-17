

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

// §6.9: "A multibit data object of one of these types shall be declared by
// specifying a range and is known as a vector." A `logic [7:0]` declaration
// is the canonical §6.9 vector and shall elaborate to an 8-bit variable.
TEST(ScalarAndVectorDeclaration, MultibitRangeProducesVectorWidth) {
  ElabFixture f;
  auto* design = Elaborate("module m; logic [7:0] v; endmodule\n", f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
  auto* mod = design->top_modules[0];
  ASSERT_GE(mod->variables.size(), 1u);
  EXPECT_EQ(mod->variables[0].width, 8u);
}

// §6.9: The multibit-vector rule applies to reg the same way it applies to
// logic; a packed range on reg produces a vector of the range's width.
TEST(ScalarAndVectorDeclaration, RegMultibitVectorWidth) {
  ElabFixture f;
  auto* design = Elaborate("module m; reg [3:0] r; endmodule\n", f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
  auto* mod = design->top_modules[0];
  ASSERT_GE(mod->variables.size(), 1u);
  EXPECT_EQ(mod->variables[0].width, 4u);
}

// §6.9: The multibit-vector rule applies to bit; a packed range on bit
// produces a vector of the range's width.
TEST(ScalarAndVectorDeclaration, BitMultibitVectorWidth) {
  ElabFixture f;
  auto* design = Elaborate("module m; bit [7:0] b; endmodule\n", f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
  auto* mod = design->top_modules[0];
  ASSERT_GE(mod->variables.size(), 1u);
  EXPECT_EQ(mod->variables[0].width, 8u);
}

// §6.9: The multibit-vector rule applies to a matching user-defined type
// of logic; the typedef carries the packed range and the use-site elaborates
// to the typedef's width.
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

// §6.9: The multibit-vector rule applies to an object whose type is
// implicit logic. A `var [7:0] v;` declaration omits the base type, defaults
// to logic, and carries a packed range; it shall elaborate to an 8-bit
// vector.
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

// §6.9: The scalar rule applies to a matching user-defined type of `bit`
// (a typedef of bit without a range) just as it applies to a typedef of
// logic. §6.9 explicitly enumerates "reg, logic, or bit (or as a matching
// user-defined type ...)", so the user-defined-type extension shall cover
// all three named integer kinds. The elaborator resolves the typedef and
// elaborates the variable to 1 bit.
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

// §6.9: The scalar rule applies to a matching user-defined type of `reg`.
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

// §6.9: The vector rule applies to a matching user-defined type of `bit`
// — a typedef of bit with a packed range produces a vector of that range's
// width. The §6.9 user-defined-type extension covers bit/reg/logic equally.
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

// §6.9: The vector rule applies to a matching user-defined type of `reg`.
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

// §6.9: The vector rule applies per declarator. Each declarator in a
// multi-name vector declaration is its own vector of the range's width.
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
