#include "fixture_elaborator.h"

using namespace delta;

namespace {

TEST(SimpleStateDependentPathElaboration, ParallelPathElaborates) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "module m;\n"
      "  specify\n"
      "    if (en) (a => b) = 10;\n"
      "  endspecify\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
}

// The subclause names the full form alongside the parallel form, so the
// elaborator must accept `if (cond) (srcs *> dsts)` on equal footing.
TEST(SimpleStateDependentPathElaboration, FullPathElaborates) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "module m;\n"
      "  specify\n"
      "    if (en) (a, b *> c) = 10;\n"
      "  endspecify\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
}

// Multiple simple state-dependent paths that share endpoints should all
// survive elaboration since each is an independent conditional contribution.
TEST(SimpleStateDependentPathElaboration, MultipleCoexistingPathsElaborate) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "module m;\n"
      "  specify\n"
      "    if (s1) (a => y) = 1;\n"
      "    if (s2) (a => y) = 2;\n"
      "  endspecify\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
}

}  // namespace
