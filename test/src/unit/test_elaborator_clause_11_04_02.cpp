// §11.4.2: Increment and decrement operators

#include "fixture_elaborator.h"

using namespace delta;

namespace {

// =============================================================================
// A.8.3 Expressions — Elaboration
// =============================================================================
// § inc_or_dec_expression — prefix increment elaborates
TEST(ElabA83, PrefixIncrementElaborates) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "module m;\n"
      "  logic [7:0] x;\n"
      "  initial begin x = 8'd5; ++x; end\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
}

// § inc_or_dec_expression — postfix decrement elaborates
TEST(ElabA83, PostfixDecrementElaborates) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "module m;\n"
      "  logic [7:0] x;\n"
      "  initial begin x = 8'd5; x--; end\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
}

// § inc_or_dec_operator — elaborates
TEST(ElabA86, IncOrDecElaborates) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "module m;\n"
      "  int x;\n"
      "  initial begin x = 10; ++x; x--; end\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
}

}  // namespace
