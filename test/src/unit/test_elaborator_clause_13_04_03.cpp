// §13.4.3: Constant functions

#include "fixture_elaborator.h"

using namespace delta;

namespace {

// =============================================================================
// A.8.2 Subroutine calls — Elaboration
// =============================================================================
// § constant_function_call — function call in parameter context
TEST(ElabA82, ConstantFunctionCallInParam) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "module m;\n"
      "  function int calc(int n); return n * 2; endfunction\n"
      "  localparam int P = calc(4);\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
}

}  // namespace
