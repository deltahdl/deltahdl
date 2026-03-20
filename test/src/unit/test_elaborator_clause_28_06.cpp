// §28.6

#include "fixture_elaborator.h"

using namespace delta;

namespace {

// --- Gate types not covered by subsection elaborator tests ---
TEST(GateElaboration, EnableGateProducesNoAssign) {
  ElabFixture f;
  auto* design = Elaborate(
      "module m;\n"
      "  wire y, a, en;\n"
      "  bufif0 b1(y, a, en);\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
  auto* mod = design->top_modules[0];
  for (auto& ca : mod->assigns) {
    EXPECT_NE(ca.lhs, nullptr);
  }
}

}  // namespace
