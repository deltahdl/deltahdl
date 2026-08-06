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

// §12.6: a constant expression pattern (11.2.1) may be a localparam, not just a
// literal. An integral localparam is of integral type and shall be accepted.
TEST(PatternMatching, LocalparamIntegralPatternAccepted) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "module t;\n"
      "  localparam int P = 5;\n"
      "  logic [7:0] x, y;\n"
      "  initial begin\n"
      "    x = 8'd5;\n"
      "    case(x) matches\n"
      "      P: y = 8'd1;\n"
      "      default: y = 8'd0;\n"
      "    endcase\n"
      "  end\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
}

// §12.6: a constant expression pattern (11.2.1) may also be a module parameter.
// An integral parameter is of integral type and shall be accepted.
TEST(PatternMatching, ParameterIntegralPatternAccepted) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "module t #(parameter int Q = 6);\n"
      "  logic [7:0] x, y;\n"
      "  initial begin\n"
      "    x = 8'd6;\n"
      "    case(x) matches\n"
      "      Q: y = 8'd1;\n"
      "      default: y = 8'd0;\n"
      "    endcase\n"
      "  end\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
}

// §12.6: a constant expression pattern (11.2.1) may be a constant function
// call. An integral-returning function used as a pattern is of integral type
// and shall be accepted.
TEST(PatternMatching, ConstFunctionCallIntegralPatternAccepted) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "module t;\n"
      "  logic [7:0] x, y;\n"
      "  function automatic int cf(); return 5; endfunction\n"
      "  initial begin\n"
      "    x = 8'd5;\n"
      "    case(x) matches\n"
      "      cf(): y = 8'd1;\n"
      "      default: y = 8'd0;\n"
      "    endcase\n"
      "  end\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
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

// §12.6: "Pattern identifiers shall be unique in the pattern" — the same
// identifier cannot bind in more than one position of a single pattern. Here
// the structure pattern binds `r1` twice, which is rejected.
TEST(PatternMatching, DuplicatePatternIdentifierRejected) {
  SimFixture f;
  ElaborateSrc(
      "typedef union tagged { struct { bit [3:0] a, b; } Add; } u_t;\n"
      "module t;\n"
      "  u_t u;\n"
      "  int y;\n"
      "  initial\n"
      "    case (u) matches\n"
      "      tagged Add '{.r1, .r1}: y = 1;\n"
      "      default: y = 0;\n"
      "    endcase\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(f.has_errors);
}

// §12.6: distinct pattern identifiers in a single pattern are allowed, so the
// uniqueness check does not over-reject a well-formed structure pattern.
TEST(PatternMatching, DistinctPatternIdentifiersAccepted) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "typedef union tagged { struct { bit [3:0] a, b; } Add; } u_t;\n"
      "module t;\n"
      "  u_t u;\n"
      "  int y;\n"
      "  initial\n"
      "    case (u) matches\n"
      "      tagged Add '{.r1, .r2}: y = 1;\n"
      "      default: y = 0;\n"
      "    endcase\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
}

// §12.6: the same uniqueness rule applies to a pattern used with the binary
// `matches` operator, not just a case item.
TEST(PatternMatching, DuplicatePatternIdentifierInMatchesOperatorRejected) {
  SimFixture f;
  ElaborateSrc(
      "typedef union tagged { struct { bit [3:0] a, b; } Add; } u_t;\n"
      "module t;\n"
      "  u_t u;\n"
      "  logic y;\n"
      "  initial y = u matches (tagged Add '{.r1, .r1});\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(f.has_errors);
}

}  // namespace
