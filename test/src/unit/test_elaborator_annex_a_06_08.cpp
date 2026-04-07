#include "fixture_elaborator.h"

using namespace delta;

namespace {

TEST(LoopSyntaxElaboration, ForeachMultiDimElaborates) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "module m;\n"
      "  logic [7:0] matrix [0:3][0:3];\n"
      "  initial begin\n"
      "    foreach (matrix[i, j]) matrix[i][j] = 0;\n"
      "  end\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
}

}  // namespace
