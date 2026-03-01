// Annex A.8.4: Primaries

#include "fixture_parser.h"
#include "helpers_parser_verify.h"

using namespace delta;

namespace {

// § primary — null
TEST(ParserA84, PrimaryNull) {
  auto r = Parse("module m; initial x = null; endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* rhs = FirstInitialRHS(r);
  ASSERT_NE(rhs, nullptr);
  EXPECT_EQ(rhs->kind, ExprKind::kIdentifier);
  EXPECT_EQ(rhs->text, "null");
}

// § bit_select — multi-dimensional
TEST(ParserA84, BitSelectMultiDim) {
  auto r = Parse(
      "module m;\n"
      "  logic [7:0] mem [0:3];\n"
      "  logic [7:0] x;\n"
      "  initial x = mem[2];\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* rhs = FirstInitialRHS(r);
  ASSERT_NE(rhs, nullptr);
  EXPECT_EQ(rhs->kind, ExprKind::kSelect);
}

// § select — member_identifier bit_select
TEST(ParserA84, SelectMemberBitSelect) {
  auto r = Parse(
      "module m;\n"
      "  typedef struct packed { logic [7:0] a; logic [7:0] b; } pair_t;\n"
      "  pair_t p;\n"
      "  logic x;\n"
      "  initial x = p.a[0];\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
}

}  // namespace
