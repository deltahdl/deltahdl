#include "fixture_elaborator.h"

using namespace delta;

namespace {

// §20.14.1: the seed argument of $random shall be an integral variable. An
// integer seed satisfies the rule and elaborates cleanly.
TEST(RandomSeedType, IntegralSeedIsAccepted) {
  ElabFixture f;
  Elaborate(
      "module m;\n"
      "  integer seed;\n"
      "  integer x;\n"
      "  initial x = $random(seed);\n"
      "endmodule\n",
      f);
  EXPECT_FALSE(f.has_errors);
}

// §20.14.1: a real seed is not an integral variable and is rejected.
TEST(RandomSeedType, RealSeedIsRejected) {
  ElabFixture f;
  Elaborate(
      "module m;\n"
      "  real seed;\n"
      "  integer x;\n"
      "  initial x = $random(seed);\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(f.has_errors);
}

// §20.14.1: a string seed is likewise non-integral and rejected.
TEST(RandomSeedType, StringSeedIsRejected) {
  ElabFixture f;
  Elaborate(
      "module m;\n"
      "  string seed;\n"
      "  integer x;\n"
      "  initial x = $random(seed);\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(f.has_errors);
}

// §20.14.1: the seedless form takes no argument, so it never triggers the
// integral-seed check.
TEST(RandomSeedType, SeedlessFormIsAccepted) {
  ElabFixture f;
  Elaborate(
      "module m;\n"
      "  integer x;\n"
      "  initial x = $random;\n"
      "endmodule\n",
      f);
  EXPECT_FALSE(f.has_errors);
}

}  // namespace
