// §31.4.6: $nochange

#include "fixture_elaborator.h"

using namespace delta;

namespace {

// =============================================================================
// A.7.5.2 Elab — mintypmax timing check limits ($nochange offsets)
// =============================================================================
TEST(ElabA70502, NochangeMinTypMaxOffsetsElaborate) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "module m;\n"
      "  specify\n"
      "    $nochange(posedge clk, data, 1:2:3, 4:5:6);\n"
      "  endspecify\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
}

}  // namespace
