// §31.5: Edge-control specifiers

#include "fixture_elaborator.h"

using namespace delta;

namespace {

// edge_control_specifier with x transitions elaborates
TEST(ElabA70503, EdgeControlSpecifierXTransitionsElaborates) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "module m;\n"
      "  specify\n"
      "    $setup(data, edge [x0, x1] clk, 10);\n"
      "  endspecify\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
}

// =============================================================================
// A.7.5.3 Elab — edge_control_specifier
// =============================================================================
// edge_control_specifier with 01, 10 descriptors elaborates
TEST(ElabA70503, EdgeControlSpecifier01_10Elaborates) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "module m;\n"
      "  specify\n"
      "    $setup(data, edge [01, 10] clk, 10);\n"
      "  endspecify\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
}

// timing_check_event with edge keyword elaborates
TEST(ElabA70503, TimingCheckEventEdgeKeywordElaborates) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "module m;\n"
      "  specify\n"
      "    $setup(data, edge clk, 10);\n"
      "  endspecify\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
}

}  // namespace
