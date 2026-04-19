#include "fixture_elaborator.h"

using namespace delta;

namespace {

TEST(EdgeSensitiveStateDependentPathElaboration, FullPathWithDataSourceElaborates) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "module m;\n"
      "  specify\n"
      "    if (en) (posedge clk *> (q : d)) = 5;\n"
      "  endspecify\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
}

// Two edge-sensitive state-dependent declarations targeting the same port
// are a legal configuration when the edge makes each unique.
TEST(EdgeSensitiveStateDependentPathElaboration, CoexistingUniqueByEdgeElaborates) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "module m;\n"
      "  specify\n"
      "    if (c) (posedge clk => q) = 1;\n"
      "    if (c) (negedge clk => q) = 2;\n"
      "  endspecify\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
}

// Two edge-sensitive state-dependent declarations targeting the same port
// and edge are legal when the condition makes each unique.
TEST(EdgeSensitiveStateDependentPathElaboration, CoexistingUniqueByConditionElaborates) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "module m;\n"
      "  specify\n"
      "    if (c1) (posedge clk => q) = 1;\n"
      "    if (c2) (posedge clk => q) = 2;\n"
      "  endspecify\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
}

}  // namespace
