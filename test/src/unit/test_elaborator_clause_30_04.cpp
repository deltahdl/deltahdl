#include "fixture_elaborator.h"

using namespace delta;

namespace {

// Every path_declaration alternative — simple parallel, simple full,
// edge-sensitive, state-dependent with if, state-dependent with ifnone —
// must elaborate cleanly in a single specify block.
TEST(SpecifyPathElaboration, AllPathTypesElaborate) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "module m;\n"
      "  specify\n"
      "    (a => b) = 5;\n"
      "    (c, d *> e) = 10;\n"
      "    (posedge clk => q) = 3;\n"
      "    if (en) (a => b) = 8;\n"
      "    ifnone (a => b) = 15;\n"
      "  endspecify\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
}

// Multiple sources may target the same destination with a distinct delay
// assigned to each source→destination path. All such declarations must
// elaborate side-by-side in a single specify block.
TEST(SpecifyPathElaboration, MultipleSourcesSameDestinationElaborates) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "module m(input a, b, c, d, output q);\n"
      "  specify\n"
      "    (a => q) = 10;\n"
      "    (b => q) = 12;\n"
      "    (c => q) = 18;\n"
      "    (d => q) = 22;\n"
      "  endspecify\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
}

}  // namespace
