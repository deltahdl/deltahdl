// Non-LRM tests

#include "fixture_elaborator.h"

using namespace delta;

namespace {

TEST(GateElaboration, AllElaborableGatesThroughFullPipeline) {
  EXPECT_TRUE(ElabOk(
      "module m;\n"
      "  wire a, b, c, y1, y2, y3, y4, y5, y6, o1, o2, n1, n2;\n"
      "  and (y1, a, b);\n"
      "  nand (y2, a, b);\n"
      "  or (y3, a, b);\n"
      "  nor (y4, a, b);\n"
      "  xor (y5, a, b);\n"
      "  xnor (y6, a, b);\n"
      "  buf (o1, a);\n"
      "  not (o2, a);\n"
      "  pullup (n1);\n"
      "  pulldown (n2);\n"
      "endmodule\n"));
}

}  // namespace
