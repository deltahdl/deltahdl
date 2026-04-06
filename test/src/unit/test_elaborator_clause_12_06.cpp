#include "fixture_simulator.h"

using namespace delta;

namespace {

TEST(CaseMatchesElaboration, CaseMatchesElaborates) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "module t;\n"
      "  logic [7:0] x, y;\n"
      "  initial begin\n"
      "    x = 8'd5;\n"
      "    case(x) matches\n"
      "      8'd5: y = 8'd10;\n"
      "      default: y = 8'd0;\n"
      "    endcase\n"
      "  end\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
}

TEST(CaseMatchesElaboration, CaseMatchesWithGuardElaborates) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "module t;\n"
      "  logic [7:0] x, y;\n"
      "  logic guard;\n"
      "  initial begin\n"
      "    x = 8'd5;\n"
      "    guard = 1'b1;\n"
      "    case(x) matches\n"
      "      8'd5 &&& guard: y = 8'd10;\n"
      "      default: y = 8'd0;\n"
      "    endcase\n"
      "  end\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
}

}  // namespace
