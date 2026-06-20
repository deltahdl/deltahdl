#include "fixture_elaborator.h"

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
  EXPECT_TRUE(f.has_errors);
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
  EXPECT_TRUE(f.has_errors);
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
  EXPECT_TRUE(f.has_errors);
}

}  // namespace
