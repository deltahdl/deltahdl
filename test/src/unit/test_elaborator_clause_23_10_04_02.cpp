#include "fixture_elaborator.h"

using namespace delta;

namespace {

TEST(DefparamEarlyNameResolution, AmbiguityWithNamedGenerateBlockIsError) {
  ElabFixture f;
  ElaborateSrc(
      "module m;\n"
      "  m1 n();\n"
      "endmodule\n"
      "module m1;\n"
      "  parameter p = 2;\n"
      "  defparam m.n.p = 1;\n"
      "  if (p == 1) begin : m\n"
      "    m2 n();\n"
      "  end\n"
      "endmodule\n"
      "module m2;\n"
      "  parameter p = 3;\n"
      "endmodule\n",
      f, "m");
  EXPECT_TRUE(f.has_errors);
}

TEST(DefparamEarlyNameResolution, RenamedGenerateBlockRemovesAmbiguity) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "module m;\n"
      "  m1 n();\n"
      "endmodule\n"
      "module m1;\n"
      "  parameter p = 2;\n"
      "  defparam m.n.p = 1;\n"
      "  if (p == 1) begin : gen_unique\n"
      "    m2 n();\n"
      "  end\n"
      "endmodule\n"
      "module m2;\n"
      "  parameter p = 3;\n"
      "endmodule\n",
      f, "m");
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
}

// The early-resolution hazard only exists when the defparam's leading name also
// names an outer scope (here, a top-level module). A generate block whose name
// merely matches the leading path component, with no like-named outer scope, is
// an ordinary unresolved target -- not an early/late divergence -- so it must
// not raise the §23.10.4.2 error.
TEST(DefparamEarlyNameResolution,
     BlockNameWithoutMatchingTopScopeIsNotAmbiguous) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "module top;\n"
      "  worker w();\n"
      "endmodule\n"
      "module worker;\n"
      "  parameter p = 2;\n"
      "  defparam blk.sub.p = 1;\n"
      "  if (p == 1) begin : blk\n"
      "    leaf sub();\n"
      "  end\n"
      "endmodule\n"
      "module leaf;\n"
      "  parameter p = 3;\n"
      "endmodule\n",
      f, "top");
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
}

}  // namespace
