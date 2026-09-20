#include <gtest/gtest.h>

#include "elaborator/rtlir.h"
#include "fixture_elaborator.h"
#include "helpers_param_value.h"

using namespace delta;

namespace {

// §20.6.2 (printed page 629): a typedef name that stands for a queue has no
// fixed size, so `$bits(qt)` written in a parameter's value is left to the
// run -- the typedef table the fold reads holds the element type alone, and
// the name is among those the elaborator records as standing for an unpacked
// aggregate -- rather than sized as one 8-bit element.
TEST(BitsOfDeclaration, QueueTypedefNameIsLeftToTheRun) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "module m;\n"
      "  typedef byte qt[$];\n"
      "  localparam int BQ = $bits(qt);\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_TRUE(ParamUnresolved(design, "BQ"));
}

}  // namespace
