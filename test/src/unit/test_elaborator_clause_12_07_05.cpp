// §12.7.5: The do...while-loop

#include "fixture_elaborator.h"

using namespace delta;

namespace {

// §12.7.5: do-while loop elaborates without error
TEST(ElabA608, DoWhileLoop) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "module m;\n"
      "  logic [7:0] x;\n"
      "  initial begin\n"
      "    do x = x + 8'd1; while (x < 8'd10);\n"
      "  end\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
}

}  // namespace
