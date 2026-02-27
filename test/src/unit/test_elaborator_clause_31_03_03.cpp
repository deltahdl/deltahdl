// §31.3.3: $setuphold

#include "fixture_elaborator.h"

using namespace delta;

namespace {

// =============================================================================
// A.7.5.1 $setuphold_timing_check — full 9-argument form
// =============================================================================
TEST(ElabA70501, SetupholdFullArgsElaborates) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "module m;\n"
      "  specify\n"
      "    $setuphold(posedge clk, data, 10, 5, ntfr, , , dCLK, dDATA);\n"
      "  endspecify\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
}

// =============================================================================
// A.7.5.2 Elab — mintypmax timecheck_condition
// =============================================================================
TEST(ElabA70502, TimecheckCondMinTypMaxElaborates) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "module m;\n"
      "  specify\n"
      "    $setuphold(posedge clk, data, 10, 5, ntfr, 1:2:3, 4:5:6);\n"
      "  endspecify\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
}

}  // namespace
