#include "fixture_elaborator.h"

using namespace delta;

namespace {

// Distinct values confirm that the third delay — not the first or second —
// becomes decay_ticks (the parent-clause test uses #(0,0,50), which cannot
// catch a wrong-slot bug).
TEST(ChargeDecaySpecElaboration, ThirdDelayFlowsToDecayTicks) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "module t;\n"
      "  trireg #(7, 11, 13) cap;\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
  auto* mod = design->top_modules[0];
  bool found = false;
  for (const auto& net : mod->nets) {
    if (net.name == "cap") {
      EXPECT_EQ(net.decay_ticks, 13u);
      found = true;
    }
  }
  EXPECT_TRUE(found);
}

// A single delay is the common propagation delay, never the charge decay:
// decay_ticks must stay at the ideal-storage default (0) even when the
// value numerically matches a plausible decay.
TEST(ChargeDecaySpecElaboration, SingleDelayDoesNotPopulateDecayTicks) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "module t;\n"
      "  trireg #50 cap;\n"
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

// Pair with the parser-level parenthesized single-delay case: even via the
// paren branch, a one-delay spec cannot produce a charge decay.
TEST(ChargeDecaySpecElaboration, ParenthesizedSingleDelayDoesNotPopulateDecayTicks) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "module t;\n"
      "  trireg #(50) cap;\n"
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

// A two-delay form covers rise and fall only; without a third delay the
// charge-decay slot is unspecified and decay_ticks stays ideal.
TEST(ChargeDecaySpecElaboration, TwoDelaysDoNotPopulateDecayTicks) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "module t;\n"
      "  trireg #(4, 9) cap;\n"
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
