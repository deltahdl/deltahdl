#include "fixture_simulator.h"

using namespace delta;

namespace {

TEST(IfMatchesElaboration, IfMatchesElaborates) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "module t;\n"
      "  logic [7:0] x, y;\n"
      "  initial begin\n"
      "    x = 8'd5;\n"
      "    if (x matches 8'd5) y = 8'd1;\n"
      "    else y = 8'd0;\n"
      "  end\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
}

TEST(IfMatchesElaboration, IfMatchesWithGuardElaborates) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "module t;\n"
      "  logic [7:0] x, y;\n"
      "  logic en;\n"
      "  initial begin\n"
      "    x = 8'd5;\n"
      "    en = 1'b1;\n"
      "    if (x matches 8'd5 &&& en) y = 8'd1;\n"
      "    else y = 8'd0;\n"
      "  end\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
}

}  // namespace
