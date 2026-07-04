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

// Claim: an argument may be an expression that returns a value, not only a
// string literal. Here the value-returning argument is a read of a declared
// variable -- a distinct argument form from the constant literal above, built
// from real module and net declaration syntax so that elaboration must resolve
// the reference and accept the call.
TEST(SubroutineCallExprElaboration,
     SystemTaskDisplayVariableArgumentElaborates) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "module m;\n"
      "  reg [7:0] v;\n"
      "  initial $display(\"v=%d\", v);\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
}

}  // namespace
