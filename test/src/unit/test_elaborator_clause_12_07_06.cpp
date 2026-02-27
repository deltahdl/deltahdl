// §12.7.6: The forever-loop

#include "fixture_elaborator.h"

using namespace delta;

namespace {

// §12.7.7: forever loop elaborates without error
TEST(ElabA608, ForeverLoop) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "module m;\n"
      "  logic [7:0] x;\n"
      "  initial begin\n"
      "    forever begin\n"
      "      if (x == 8'd10) break;\n"
      "      x = x + 8'd1;\n"
      "    end\n"
      "  end\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
}

}  // namespace
