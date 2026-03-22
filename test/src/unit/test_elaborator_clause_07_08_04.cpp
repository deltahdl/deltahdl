#include "elaborator/elaborator.h"
#include "elaborator/rtlir.h"
#include "fixture_elaborator.h"

using namespace delta;

namespace {

TEST(IntegralIndexAssocArrayElaboration, AssocArrayByteIndexWidth) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "module top;\n"
      "  int map[byte];\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  ASSERT_FALSE(design->top_modules.empty());
  auto& vars = design->top_modules[0]->variables;
  ASSERT_FALSE(vars.empty());
  EXPECT_TRUE(vars[0].is_assoc);
  EXPECT_EQ(vars[0].assoc_index_width, 8u);
}

TEST(IntegralIndexAssocArrayElaboration, AssocArrayIntIndexWidth) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "module top;\n"
      "  int map[int];\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  ASSERT_FALSE(design->top_modules.empty());
  auto& vars = design->top_modules[0]->variables;
  ASSERT_FALSE(vars.empty());
  EXPECT_TRUE(vars[0].is_assoc);
  EXPECT_EQ(vars[0].assoc_index_width, 32u);
}

TEST(IntegralIndexAssocArrayElaboration, AssocArrayShortintIndexWidth) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "module top;\n"
      "  int map[shortint];\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  auto& vars = design->top_modules[0]->variables;
  ASSERT_FALSE(vars.empty());
  EXPECT_TRUE(vars[0].is_assoc);
  EXPECT_EQ(vars[0].assoc_index_width, 16u);
}

TEST(IntegralIndexAssocArrayElaboration, AssocArrayLongintIndexWidth) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "module top;\n"
      "  int map[longint];\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  auto& vars = design->top_modules[0]->variables;
  ASSERT_FALSE(vars.empty());
  EXPECT_TRUE(vars[0].is_assoc);
  EXPECT_EQ(vars[0].assoc_index_width, 64u);
}

TEST(IntegralIndexAssocArrayElaboration, AssocArrayIntegerIndexWidth) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "module top;\n"
      "  int map[integer];\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  auto& vars = design->top_modules[0]->variables;
  ASSERT_FALSE(vars.empty());
  EXPECT_TRUE(vars[0].is_assoc);
  EXPECT_EQ(vars[0].assoc_index_width, 32u);
}

TEST(IntegralIndexAssocArrayElaboration, NotStringIndex) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "module top;\n"
      "  int map[int];\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  auto& v = design->top_modules[0]->variables[0];
  EXPECT_FALSE(v.is_string_index);
  EXPECT_FALSE(v.is_wildcard_index);
}

}  // namespace
