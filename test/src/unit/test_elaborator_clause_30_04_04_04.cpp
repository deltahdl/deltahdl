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

TEST(IfnoneConditionElaboration, FullPathElaborates) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "module m;\n"
      "  specify\n"
      "    ifnone (a, b *> c) = 10;\n"
      "  endspecify\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
}

// R3: ifnone source/destination must match companion if(cond) paths.
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

// R5: cannot mix ifnone with an unconditional path on the same endpoints.
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
