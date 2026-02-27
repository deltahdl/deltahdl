// §30.4.6: Declaring multiple module paths in a single statement

#include "fixture_elaborator.h"

using namespace delta;

namespace {

// Mixed terminal forms together elaborate
TEST(ElabA703, MixedTerminalFormsElaborate) {
  ElabA703Fixture f;
  auto* design = ElaborateSrc(
      "module m;\n"
      "  specify\n"
      "    (a, b[3], intf.sig[7:0] *> x[0], y, intf2.out) = 5;\n"
      "  endspecify\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
}

}  // namespace
