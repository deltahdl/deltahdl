#include "fixture_elaborator.h"
#include "helpers_reported_error.h"

using namespace delta;

namespace {

TEST(IfnoneConditionElaboration, ParallelPathElaborates) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "module m;\n"
      "  specify\n"
      "    ifnone (a => b) = 15;\n"
      "  endspecify\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
}

// C1 (positive): an ifnone path whose source and destination match a companion
// state-dependent path satisfies the same-endpoints requirement, so the design
// elaborates cleanly. This exercises the accept side of the endpoint match,
// distinct from the lone-ifnone case where there are no companions at all.
TEST(IfnoneConditionElaboration, MatchingCompanionElaborates) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "module m;\n"
      "  specify\n"
      "    if (c) (a => y) = 1;\n"
      "    ifnone (a => y) = 2;\n"
      "  endspecify\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
}

// C2 (bullet 2): a corresponding state-dependent path may be edge-sensitive as
// well as simple. Here the ifnone path's only companion is an edge-sensitive
// state-dependent path (§30.4.3 syntax) that shares the same source and
// destination, so the same-endpoints requirement is satisfied and the design
// elaborates cleanly. This observes at the elaboration stage that the endpoint
// match admits an edge-sensitive companion, which the parser-stage coexistence
// test cannot show because endpoint matching runs only during elaboration.
TEST(IfnoneConditionElaboration, MatchingEdgeSensitiveCompanionElaborates) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "module m;\n"
      "  specify\n"
      "    if (c) (posedge clk => q) = (1, 2);\n"
      "    ifnone (clk => q) = (3, 4);\n"
      "  endspecify\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
}

TEST(IfnoneConditionElaboration, ErrorEndpointMismatch) {
  ElabFixture f;
  ElaborateSrc(
      "module m;\n"
      "  specify\n"
      "    if (c) (a => y) = 1;\n"
      "    ifnone (b => y) = 2;\n"
      "  endspecify\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "do not match any companion state-dependent path",
                            4, "30.4.4.4"));
}

// C1 (destination half): the same-endpoints requirement covers the destination
// as well as the source. Here the source matches the companion but the
// destination differs, so the ifnone path has no matching companion and is
// rejected. ErrorEndpointMismatch differs in the source; this differs only in
// the destination, exercising the destination comparison branch.
TEST(IfnoneConditionElaboration, ErrorDestinationMismatch) {
  ElabFixture f;
  ElaborateSrc(
      "module m;\n"
      "  specify\n"
      "    if (c) (a => y) = 1;\n"
      "    ifnone (a => z) = 2;\n"
      "  endspecify\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "do not match any companion state-dependent path",
                            4, "30.4.4.4"));
}

TEST(IfnoneConditionElaboration, ErrorCoexistsWithUnconditional) {
  ElabFixture f;
  ElaborateSrc(
      "module m;\n"
      "  specify\n"
      "    ifnone (a => b) = 1;\n"
      "    (a => b) = 2;\n"
      "  endspecify\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(ReportedError(
      f.diag.Diagnostics(),
      "conflicts with an unconditional path on the same endpoints", 3,
      "30.4.4.4"));
}

// Claim A (multi-terminal endpoints): the same-endpoints requirement compares
// full source and destination terminal lists, not just single terminals. A
// full-connection ifnone with two source terminals (§30.4.2/§30.4.5 syntax)
// matches its full-connection state-dependent companion only when every source
// and destination terminal agrees, exercising the multi-terminal comparison
// loop that the single-terminal match tests do not reach.
TEST(IfnoneConditionElaboration, MatchingFullConnectionCompanionElaborates) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "module m;\n"
      "  specify\n"
      "    if (c) (a, b *> z) = 10;\n"
      "    ifnone (a, b *> z) = 20;\n"
      "  endspecify\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
}

// Claim E (bullet 4) forbids specifying both an ifnone and an unconditional
// path only for the SAME module path. An unconditional path with a different
// source and destination is a distinct module path, so it may coexist with the
// ifnone without error. This observes that the conflict check is scoped by
// endpoints, the accept boundary of the rule whose reject side is
// ErrorCoexistsWith- Unconditional.
TEST(IfnoneConditionElaboration, UnrelatedUnconditionalCoexists) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "module m;\n"
      "  specify\n"
      "    ifnone (a => b) = 1;\n"
      "    (c => d) = 2;\n"
      "  endspecify\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
}

}  // namespace
