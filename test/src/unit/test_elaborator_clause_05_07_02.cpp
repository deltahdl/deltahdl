// §5.7.2: Real literal constants

#include "fixture_elaborator.h"

using namespace delta;

namespace {

// § real_number — fixed_point_number elaborates
TEST(ElabA87, FixedPointElaborates) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "module m;\n"
      "  real x;\n"
      "  initial x = 2.718;\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
}

// § real_number — scientific notation elaborates
TEST(ElabA87, ScientificNotationElaborates) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "module m;\n"
      "  real x;\n"
      "  initial x = 1.5e+3;\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
}

}  // namespace
