// §12.7.4: The while-loop

#include "fixture_elaborator.h"

using namespace delta;

namespace {

// §12.7.4: while loop elaborates without error
TEST(ElabA608, WhileLoop) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "module m;\n"
      "  logic [7:0] x;\n"
      "  initial begin\n"
      "    while (x > 0) x = x - 8'd1;\n"
      "  end\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
}

}  // namespace
