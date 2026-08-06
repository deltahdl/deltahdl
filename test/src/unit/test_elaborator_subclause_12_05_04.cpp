#include "fixture_simulator.h"

using namespace delta;

namespace {

TEST(CaseInsideElaboration, CaseInsideElaborates) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "module t;\n"
      "  logic [7:0] x, y;\n"
      "  initial begin\n"
      "    x = 8'd5;\n"
      "    case(x) inside\n"
      "      [8'd0:8'd3]: y = 8'd1;\n"
      "      [8'd4:8'd7]: y = 8'd2;\n"
      "      default: y = 8'd0;\n"
      "    endcase\n"
      "  end\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
}

}  // namespace
