// §30.4.7.2: Positive polarity

#include "fixture_elaborator.h"

using namespace delta;

namespace {

// Path with polarity operator elaborates
TEST(ElabA702, PathWithPolarityElaborates) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "module m;\n"
      "  specify\n"
      "    (a + => b) = 5;\n"
      "  endspecify\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
}

}  // namespace
