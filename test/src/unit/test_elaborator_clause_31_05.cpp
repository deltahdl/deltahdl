#include "fixture_elaborator.h"

using namespace delta;

namespace {

// §31.5: the bare `edge` keyword (with no descriptor list) elaborates as a
// valid event control on a timing check data event.
TEST(EdgeControlSpecifierElaboration, EdgeKeywordElaborates) {
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

// §31.5 Syntax 31-15: an `edge [01, 10]` descriptor list elaborates cleanly
// alongside the timing check it qualifies.
TEST(EdgeControlSpecifierElaboration, Descriptors01And10Elaborate) {
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

// §31.5 Syntax 31-15: the `z_or_x zero_or_one` form with `x` leads
// elaborates without diagnostics.
TEST(EdgeControlSpecifierElaboration, XTransitionsElaborate) {
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

// §31.5: "Edge transitions involving z are treated the same way as edge
// transitions involving x" — z-form descriptors elaborate without errors.
TEST(EdgeControlSpecifierElaboration, ZTransitionsElaborate) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "module m;\n"
      "  specify\n"
      "    $hold(edge [z0, z1] clk, data, 5);\n"
      "  endspecify\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
}

// §31.5: the edge-control specifier coexists with a §31.7
// timing_check_condition on the same event during elaboration.
TEST(EdgeControlSpecifierElaboration, EdgeKeywordWithConditionElaborates) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "module m;\n"
      "  specify\n"
      "    $setup(data, edge clk &&& en, 10);\n"
      "  endspecify\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
}

// §31.5 Syntax 31-15: the `zero_or_one z_or_x` form (e.g. `0x`, `1x`) is
// the third edge_descriptor alternative and must elaborate as cleanly as
// the other two.
TEST(EdgeControlSpecifierElaboration, ToXTransitionsElaborate) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "module m;\n"
      "  specify\n"
      "    $setup(data, edge [0x, 1x] clk, 10);\n"
      "  endspecify\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
}

}  // namespace
