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
#include "helpers_reported_error.h"

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

// §6.3.2 states "Charge strength shall only be used when declaring a net of
// type trireg", so a charge-strength keyword on any other net type is
// rejected. The report names §6.3.2.1, the subclause devoted to the charge
// strength specification, which restates the rule as "The charge strength
// specification shall be used only with trireg nets". It is raised in
// Parser::ParseNetStrength, where the specification is read, and ElaborateSrc
// leaves it in the fixture's engine.
TEST(NetStrengths, ChargeStrengthRejectedOnNonTrireg) {
  ElabFixture f;
  // The charge-strength rule is reported while parsing, so this case reaches
  // its subject through a source that does not parse.
  ElaborateSrcAllowingParseErrors(
      "module t;\n"
      "  wire (large) w;\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "charge strength can only be used with trireg nets",
                            2, "6.3.2.1"));
}

// §6.3.2 states "Drive strength shall only be used when placing a continuous
// assignment on a net in the same statement that declares the net", so a
// declaration carrying a strength and no assignment is rejected. §6.3.2 is the
// subclause the report names: §6.3.2.2 says only that the specification
// "allows" the assignment, and §10.3.4 says only where a strength may be
// written and that it applies to scalar nets.
TEST(NetStrengths, DriveStrengthRejectedWithoutAssignment) {
  ElabFixture f;
  Elaborate(
      "module t;\n"
      "  wire (strong0, weak1) w;\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(ReportedError(
      f.diag.Diagnostics(),
      "drive strength on net declaration requires an assignment", 2, "6.3.2"));
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
