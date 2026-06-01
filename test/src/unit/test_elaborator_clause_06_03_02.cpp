// Canonical tests for §6.3.2 "Strengths".
//
// §6.3.2 names two restrictions on the strengths that a net declaration may
// carry:
//   - Charge strength may be used only when the declared net is a trireg.
//   - Drive strength may be used only when the same statement that declares
//     the net also places a continuous assignment on it.
// Both restrictions are enforced by the elaborator, so they are observed here.
// The keyword set, default charge strength, and the drive-strength semantics
// themselves belong to the descendant subclauses §6.3.2.1 and §6.3.2.2.

#include <gtest/gtest.h>

#include "fixture_elaborator.h"

using namespace delta;

namespace {

// §6.3.2: charge strength is permitted on a trireg net, and the elaborator
// records it on the net rather than rejecting the declaration.
TEST(NetStrengths, ChargeStrengthAcceptedOnTrireg) {
  ElabFixture f;
  auto* design = Elaborate(
      "module t;\n"
      "  trireg (large) cap;\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
  auto* mod = design->top_modules[0];
  bool found = false;
  for (const auto& net : mod->nets) {
    if (net.name == "cap") {
      EXPECT_EQ(net.charge_strength, Strength::kLarge);
      found = true;
    }
  }
  EXPECT_TRUE(found);
}

// §6.3.2: charge strength shall only be used when declaring a trireg net, so a
// charge-strength keyword on any other net type is rejected.
TEST(NetStrengths, ChargeStrengthRejectedOnNonTrireg) {
  ElabFixture f;
  Elaborate(
      "module t;\n"
      "  wire (large) w;\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(f.has_errors);
}

// §6.3.2: drive strength shall only be used when the declaring statement also
// places a continuous assignment on the net; without one the declaration is
// rejected.
TEST(NetStrengths, DriveStrengthRejectedWithoutAssignment) {
  ElabFixture f;
  Elaborate(
      "module t;\n"
      "  wire (strong0, weak1) w;\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(f.has_errors);
}

// §6.3.2: drive strength is permitted when the same statement that declares
// the net also continuously assigns to it.
TEST(NetStrengths, DriveStrengthAcceptedWithAssignment) {
  ElabFixture f;
  Elaborate(
      "module t;\n"
      "  wire (strong0, weak1) w = 1'b0;\n"
      "endmodule\n",
      f);
  EXPECT_FALSE(f.has_errors);
}

}  // namespace
