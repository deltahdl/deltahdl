// §7.8.1: Wildcard index type


#include "elaborator/elaborator.h"
#include "elaborator/rtlir.h"

#include "fixture_elaborator.h"

using namespace delta;

namespace {

TEST(ParserA25, AssocDimElaboratesWildcard) {
  ElabFixture f;
  auto* design = Elaborate("module m; int aa [*]; endmodule\n", f);
  ASSERT_NE(design, nullptr);
  auto* mod = design->top_modules[0];
  ASSERT_GE(mod->variables.size(), 1u);
  EXPECT_TRUE(mod->variables[0].is_assoc);
}

}  // namespace
