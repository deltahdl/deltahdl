// §16.14.5: Using concurrent assertion statements outside procedural code

#include "fixture_elaborator.h"

using namespace delta;

namespace {

// concurrent assert property at module level elaborates
TEST(ElabA610, AssertPropertyElaborates) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "module m;\n"
      "  assert property (1);\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
}

}  // namespace
