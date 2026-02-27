// Annex A.8.2: Subroutine calls

#include "fixture_elaborator.h"

using namespace delta;

namespace {

// § method_call — method call elaborates
TEST(ElabA82, MethodCallElaborates) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "module m;\n"
      "  initial begin obj.method(); end\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
}

}  // namespace
