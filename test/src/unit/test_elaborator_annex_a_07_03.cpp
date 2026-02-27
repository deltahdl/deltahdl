// Annex A.7.3: Specify block terminals

#include "fixture_elaborator.h"

using namespace delta;

namespace {

// Dotted terminal with range elaborates
TEST(ElabA703, DottedTerminalWithRangeElaborates) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "module m;\n"
      "  specify\n"
      "    (intf.sig[3:0] => intf.out[7:0]) = 5;\n"
      "  endspecify\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
}

}  // namespace
