#include "fixture_simulator.h"

using namespace delta;

namespace {

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

// §12.6: "A constant expression pattern shall be of integral type."
TEST(PatternMatching, RealLiteralPatternRejected) {
  SimFixture f;
  ElaborateSrc(
      "module t;\n"
      "  real r;\n"
      "  int y;\n"
      "  initial begin\n"
      "    r = 1.5;\n"
      "    case(r) matches\n"
      "      1.5: y = 1;\n"
      "      default: y = 0;\n"
      "    endcase\n"
      "  end\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(f.has_errors);
}

// §12.6: same rule applied to the binary `matches` operator.
TEST(PatternMatching, RealLiteralPatternInMatchesOperatorRejected) {
  SimFixture f;
  ElaborateSrc(
      "module t;\n"
      "  real r;\n"
      "  logic y;\n"
      "  initial begin\n"
      "    r = 1.5;\n"
      "    y = r matches 2.5;\n"
      "  end\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(f.has_errors);
}

// §12.6: a string literal is not of integral type, so it is also rejected
// when used as a constant expression pattern.
TEST(PatternMatching, StringLiteralPatternRejected) {
  SimFixture f;
  ElaborateSrc(
      "module t;\n"
      "  string s;\n"
      "  logic y;\n"
      "  initial begin\n"
      "    s = \"hi\";\n"
      "    y = s matches \"hi\";\n"
      "  end\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(f.has_errors);
}

// §12.6: integer literal pattern is integral and shall be accepted.
TEST(PatternMatching, IntegerLiteralPatternAccepted) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "module t;\n"
      "  logic [7:0] x, y;\n"
      "  initial begin\n"
      "    x = 8'd5;\n"
      "    case(x) matches\n"
      "      8'd5: y = 8'd1;\n"
      "      8'd6: y = 8'd2;\n"
      "      default: y = 8'd0;\n"
      "    endcase\n"
      "  end\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
}

}  // namespace
