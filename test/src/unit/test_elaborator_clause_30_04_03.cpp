#include "fixture_elaborator.h"

using namespace delta;

// Clause 30.4.3 defines no elaborator-stage rule of its own: a module path's
// source/destination restrictions are owned by 30.4.1 and the full/parallel
// width rules by 30.4.5. These remain as smoke coverage confirming that the
// edge-sensitive path constructs (edge identifier, data source expression)
// flow through elaboration without spurious diagnostics. The data-source case
// additionally exercises the elaborator's data_source-present branch, which is
// skipped by the 30.4.5 parallel width check.
namespace {

TEST(SpecifyPathElaboration, EdgeSensitivePathElaborates) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "module m;\n"
      "  specify\n"
      "    (posedge clk => q) = 5;\n"
      "  endspecify\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
}

TEST(SpecifyPathElaboration, EdgeSensitiveWithDataSourceElaborates) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "module m;\n"
      "  specify\n"
      "    (posedge clk => (q : d)) = 5;\n"
      "  endspecify\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
}

}  // namespace
