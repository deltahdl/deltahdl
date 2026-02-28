// §7.8.2: String index

#include "elaborator/elaborator.h"
#include "elaborator/rtlir.h"
#include "fixture_elaborator.h"

using namespace delta;

namespace {

TEST(ParserA25, AssocDimElaboratesStringIndex) {
  ElabFixture f;
  auto* design = Elaborate("module m; int aa [string]; endmodule\n", f);
  ASSERT_NE(design, nullptr);
  auto* mod = design->top_modules[0];
  ASSERT_GE(mod->variables.size(), 1u);
  EXPECT_TRUE(mod->variables[0].is_assoc);
  EXPECT_TRUE(mod->variables[0].is_string_index);
}

}  // namespace
