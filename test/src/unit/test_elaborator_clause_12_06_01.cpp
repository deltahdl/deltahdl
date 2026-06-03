#include "fixture_simulator.h"

using namespace delta;

namespace {

TEST(CaseMatchesItemElaboration, CaseMatchesItemElaborates) {
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
  EXPECT_FALSE(f.has_errors);
}

TEST(CaseMatchesItemElaboration, CaseMatchesGuardElaborates) {
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

// §12.6.1: the tested expression shall have a known type that is the same as
// the type of the pattern in each case item. A real-valued selector cannot
// share a type with an integral constant pattern, so the pairing is rejected.
TEST(CaseMatchesItemElaboration, RealSelectorWithIntegralPatternRejected) {
  SimFixture f;
  ElaborateSrc(
      "module t;\n"
      "  real r;\n"
      "  logic [7:0] y;\n"
      "  initial begin\n"
      "    r = 1.0;\n"
      "    case(r) matches\n"
      "      8'd5: y = 8'd10;\n"
      "      default: y = 8'd0;\n"
      "    endcase\n"
      "  end\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(f.has_errors);
}

// §12.6.1: the type check looks through a `&&&` filter to the pattern itself,
// so a real selector paired with a guarded integral pattern is still rejected.
TEST(CaseMatchesItemElaboration, RealSelectorWithGuardedIntegralPatternRejected) {
  SimFixture f;
  ElaborateSrc(
      "module t;\n"
      "  real r;\n"
      "  logic [7:0] y;\n"
      "  logic en;\n"
      "  initial begin\n"
      "    r = 1.0;\n"
      "    en = 1'b1;\n"
      "    case(r) matches\n"
      "      8'd5 &&& en: y = 8'd10;\n"
      "      default: y = 8'd0;\n"
      "    endcase\n"
      "  end\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(f.has_errors);
}

}
