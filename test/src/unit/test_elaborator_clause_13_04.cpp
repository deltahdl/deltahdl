// §13.4: Functions


#include "elaboration/elaborator.h"
#include "elaboration/rtlir.h"

#include "fixture_elaborator.h"

using namespace delta;

namespace {

// § function_subroutine_call — in continuous assignment
TEST(ElabA82, FunctionCallInContAssign) {
  ElabA82Fixture f;
  auto* design = ElaborateSrc(
      "module m;\n"
      "  wire [7:0] y;\n"
      "  function logic [7:0] compute(input logic [7:0] a);\n"
      "    return a + 8'd1;\n"
      "  endfunction\n"
      "  assign y = compute(8'd5);\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
}

// Elab test fixture
// §13.4.4: fork/join is illegal inside a function
TEST(ElabA603, ForkJoinIllegalInFunction) {
  ElabFixture f;
  ElaborateSrc(
      "module m;\n"
      "  function void my_func();\n"
      "    fork\n"
      "      a = 1;\n"
      "    join\n"
      "  endfunction\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(f.has_errors);
}

}  // namespace
