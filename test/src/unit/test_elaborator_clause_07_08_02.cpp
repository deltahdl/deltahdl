#include "elaborator/elaborator.h"
#include "elaborator/rtlir.h"
#include "fixture_elaborator.h"

using namespace delta;

namespace {

TEST(StringIndexAssocArrayElaboration, AssocDimElaboratesStringIndex) {
  ElabFixture f;
  auto* design = Elaborate("module m; int aa [string]; endmodule\n", f);
  ASSERT_NE(design, nullptr);
  auto* mod = design->top_modules[0];
  ASSERT_GE(mod->variables.size(), 1u);
  EXPECT_TRUE(mod->variables[0].is_assoc);
  EXPECT_TRUE(mod->variables[0].is_string_index);
}

// §7.8.2: String-indexed array is not wildcard.
TEST(StringIndexAssocArrayElaboration, NotWildcardIndex) {
  ElabFixture f;
  auto* design = Elaborate("module m; int aa [string]; endmodule\n", f);
  ASSERT_NE(design, nullptr);
  auto& v = design->top_modules[0]->variables[0];
  EXPECT_FALSE(v.is_wildcard_index);
}

// §7.8.2: Vector element type with string index.
TEST(StringIndexAssocArrayElaboration, VectorElementType) {
  ElabFixture f;
  auto* design =
      Elaborate("module m; bit [7:0] aa [string]; endmodule\n", f);
  ASSERT_NE(design, nullptr);
  auto& v = design->top_modules[0]->variables[0];
  EXPECT_TRUE(v.is_assoc);
  EXPECT_TRUE(v.is_string_index);
  EXPECT_EQ(v.width, 8u);
}

}  // namespace
