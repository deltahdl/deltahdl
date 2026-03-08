#include "fixture_elaborator.h"

using namespace delta;

namespace {

TEST(ElabA610, DeferredAssertElaborates) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "module m;\n"
      "  initial assert #0 (1);\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
}

}
