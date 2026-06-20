#include "fixture_elaborator.h"

using namespace delta;

namespace {

TEST(SubroutineCallExprElaboration, SystemTaskDisplayElaborates) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "module m;\n"
      "  initial $display(\"hello %d\", 42);\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
}

}  // namespace
