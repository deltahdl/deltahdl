#include <gtest/gtest.h>

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

// §30.4.4.4: an ifnone path between the same terminals as a state-dependent
// path is that path's default delay, and the pair elaborates cleanly.
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
// well as simple. Here the ifnone path's only counterpart is an edge-sensitive
// state-dependent path (§30.4.3 syntax) between the same source and
// destination, and the design elaborates cleanly.
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

// §30.4.4.4 treats an ifnone path that no state-dependent path corresponds to
// as an unconditional simple path, so it is legal. The conditional path here
// runs from another source, which does not make it correspond, and the check
// once rejected the ifnone for it.
TEST(IfnoneConditionElaboration, IfnoneFromAnotherSourceElaborates) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "module m;\n"
      "  specify\n"
      "    if (c) (a => y) = 1;\n"
      "    ifnone (b => y) = 2;\n"
      "  endspecify\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
}

// The same rule with the destination differing: the conditional path to y does
// not correspond to the ifnone path to z, which stands as an unconditional
// path of its own.
TEST(IfnoneConditionElaboration, IfnoneToAnotherDestinationElaborates) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "module m(input a, c, output y, z);\n"
      "  specify\n"
      "    if (c) (a => y) = 1;\n"
      "    ifnone (a => z) = 2;\n"
      "  endspecify\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
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

// A full-connection ifnone with two source terminals (§30.4.2, §30.4.5) beside
// the state-dependent path between the same terminal lists elaborates cleanly.
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

// §30.4.4.4 forbids an ifnone path beside an unconditional *simple* path of the
// same module path. An edge-sensitive path is no simple path, so an
// unconditional one may stand beside the ifnone.
TEST(IfnoneConditionElaboration, UnconditionalEdgeSensitivePathCoexists) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "module m(input clk, d, output q);\n"
      "  specify\n"
      "    (posedge clk => (q : d)) = 1;\n"
      "    ifnone (clk => q) = 2;\n"
      "  endspecify\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
}

// A module's specify blocks all declare its module paths, so the ifnone and
// the unconditional path conflict when they sit in two blocks as when they
// share one.
TEST(IfnoneConditionElaboration, ConflictAcrossSpecifyBlocksIsReported) {
  ElabFixture f;
  ElaborateSrc(
      "module m(input a, output b);\n"
      "  specify\n"
      "    (a => b) = 2;\n"
      "  endspecify\n"
      "  specify\n"
      "    ifnone (a => b) = 1;\n"
      "  endspecify\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(ReportedError(
      f.diag.Diagnostics(),
      "conflicts with an unconditional path on the same endpoints", 6,
      "30.4.4.4"));
}

}  // namespace
