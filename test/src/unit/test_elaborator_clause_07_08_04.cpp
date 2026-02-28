// §7.8.4: Integral index

#include "elaborator/elaborator.h"
#include "elaborator/rtlir.h"
#include "fixture_elaborator.h"

using namespace delta;

namespace {

TEST(ParserA25, AssocDimElaboratesIndexWidth) {
  ElabFixture f;
  auto* design = Elaborate("module m; int aa [byte]; endmodule\n", f);
  ASSERT_NE(design, nullptr);
  auto* mod = design->top_modules[0];
  ASSERT_GE(mod->variables.size(), 1u);
  EXPECT_TRUE(mod->variables[0].is_assoc);
  EXPECT_EQ(mod->variables[0].assoc_index_width, 8u);
}

// §7.9.8: Assoc array index width propagated to RtlirVariable.
TEST(Elaboration, AssocArrayByteIndexWidth) {
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

TEST(Elaboration, AssocArrayIntIndexWidth) {
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

}  // namespace
