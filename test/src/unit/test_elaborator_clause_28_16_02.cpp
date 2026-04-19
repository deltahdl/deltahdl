#include "fixture_elaborator.h"

using namespace delta;

namespace {

TEST(ChargeDecayElaboration, NoDecaySpecMeansIdeal) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "module t;\n"
      "  trireg cap;\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
  auto* mod = design->top_modules[0];
  bool found = false;
  for (const auto& net : mod->nets) {
    if (net.name == "cap") {
      EXPECT_EQ(net.decay_ticks, 0u);
      found = true;
    }
  }
  EXPECT_TRUE(found);
}

}  // namespace
