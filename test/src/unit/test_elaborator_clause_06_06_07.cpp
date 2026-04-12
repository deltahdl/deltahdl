#include "fixture_elaborator.h"

using namespace delta;

namespace {

TEST(NettypeElaboration, NettypeDeclRegistersType) {
  ElabFixture f;
  auto* design = Elaborate(
      "module m;\n"
      "  nettype logic my_net;\n"
      "  my_net x;\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
  auto* mod = design->top_modules[0];
  bool found = false;
  for (const auto& n : mod->nets) {
    if (n.name == "x") found = true;
  }
  EXPECT_TRUE(found);
}

}  // namespace
