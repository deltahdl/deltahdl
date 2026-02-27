// §30.4.5: Full connection and parallel connection paths

#include "fixture_elaborator.h"

using namespace delta;

namespace {

// Simple full path elaborates
TEST(ElabA702, SimpleFullPathElaborates) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "module m;\n"
      "  specify\n"
      "    (a, b *> c) = 10;\n"
      "  endspecify\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
}

}  // namespace
