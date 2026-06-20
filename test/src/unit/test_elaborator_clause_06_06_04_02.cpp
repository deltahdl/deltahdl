#include "fixture_elaborator.h"

using namespace delta;

namespace {

TEST(ChargeDecayElaboration, DecayTimeZeroIsIdeal) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "module t;\n"
      "  trireg #(1, 1, 0) cap;\n"
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

// §6.6.4.2: a trireg without any decay delay in its declaration is in the
// ideal capacitive state and retains its value indefinitely. With no delay
// specification (and no default decay time directive in effect), the
// elaborator leaves the net's decay time at zero, marking it ideal.
TEST(ChargeDecayElaboration, PlainTriregHasNoDecay) {
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
