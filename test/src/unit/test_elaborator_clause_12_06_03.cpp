#include "fixture_simulator.h"

using namespace delta;

namespace {

TEST(TernaryMatchesElaboration, TernaryMatchesElaborates) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "module t;\n"
      "  logic [7:0] x, y;\n"
      "  initial begin\n"
      "    x = 8'd5;\n"
      "    y = (x matches 8'd5) ? 8'd42 : 8'd0;\n"
      "  end\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
}

TEST(TernaryMatchesElaboration, TernaryMatchesWithGuardElaborates) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "module t;\n"
      "  logic [7:0] x, y;\n"
      "  logic en;\n"
      "  initial begin\n"
      "    x = 8'd5;\n"
      "    en = 1'b1;\n"
      "    y = (x matches 8'd5 &&& en) ? 8'd10 : 8'd0;\n"
      "  end\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
}

// §12.6.3: a conditional-expression predicate may chain several `matches`
// clauses with `&&&`. Elaboration walks every matches operator in the ternary
// condition and type-checks each integral pattern; a clean multi-clause
// predicate must elaborate without diagnostics.
TEST(TernaryMatchesElaboration, ChainedMatchesInTernaryElaborates) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "module t;\n"
      "  logic [7:0] a, b, y;\n"
      "  logic c;\n"
      "  initial begin\n"
      "    a = 8'd1;\n"
      "    b = 8'd2;\n"
      "    c = 1'b1;\n"
      "    y = (a matches 8'd1 &&& b matches 8'd2 &&& c) ? 8'd1 : 8'd0;\n"
      "  end\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
}

}
