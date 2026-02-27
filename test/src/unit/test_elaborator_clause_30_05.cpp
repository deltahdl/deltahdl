// §30.5: Assigning delays to module paths

#include "fixture_elaborator.h"

using namespace delta;

namespace {

// Specparam reference in delay elaborates
TEST(ElabA704, SpecparamDelayElaborates) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "module m;\n"
      "  specify\n"
      "    specparam tRise = 3, tFall = 5;\n"
      "    (a => b) = (tRise, tFall);\n"
      "  endspecify\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
}

}  // namespace
