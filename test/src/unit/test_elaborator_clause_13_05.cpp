// §13.5: Subroutine calls and argument passing

#include "fixture_elaborator.h"

using namespace delta;

namespace {

// =============================================================================
// A.6.9 Subroutine call statements — Elaboration
// =============================================================================
// tf_call: task call elaborates without error
TEST(ElabA609, TfCallElaborates) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "module m;\n"
      "  logic [7:0] x;\n"
      "  task set_x;\n"
      "    x = 8'd1;\n"
      "  endtask\n"
      "  initial set_x();\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
}

// § primary — function call elaborates
TEST(ElabA84, PrimaryFunctionCallElaborates) {
  ElabA84Fixture f;
  auto* design = ElaborateSrc(
      "module m;\n"
      "  function int foo(int a); return a + 1; endfunction\n"
      "  int x;\n"
      "  initial x = foo(5);\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
}

}  // namespace
