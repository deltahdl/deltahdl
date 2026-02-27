// §6.24.1: Cast operator

#include "fixture_parser.h"

using namespace delta;

namespace {

// =============================================================================
// A.2.2.1 Net and variable types
// =============================================================================
// --- casting_type ---
// simple_type | constant_primary | signing | string | const
TEST(ParserA221, CastingTypeSimpleInt) {
  // simple_type: integer_type cast
  auto r = Parse(
      "module m;\n"
      "  initial begin int x; x = int'(3.14); end\n"
      "endmodule");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
}

TEST(ParserA221, CastingTypeSigning) {
  // signing: signed'(val)
  auto r = Parse(
      "module m;\n"
      "  initial begin int x; x = signed'(8'hFF); end\n"
      "endmodule");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
}

TEST(ParserA221, CastingTypeString) {
  // string: string'(val)
  auto r = Parse(
      "module m;\n"
      "  initial begin string s; s = string'(65); end\n"
      "endmodule");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
}

TEST(ParserA221, CastingTypeConst) {
  // const: const'(expr)
  auto r = Parse(
      "module m;\n"
      "  initial begin int x; x = const'(42); end\n"
      "endmodule");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
}

TEST(ParserA221, CastingTypeUserDefined) {
  // casting_type with user-defined type (simple_type: ps_type_identifier)
  // Note: constant_primary'(expr) cast (e.g., N'(val)) requires semantic
  // analysis to distinguish from sized literals — tested via type casts.
  auto r = Parse(
      "module m;\n"
      "  typedef logic [7:0] byte_t;\n"
      "  initial begin byte_t x; x = byte_t'(16'hFF); end\n"
      "endmodule");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
}

}  // namespace
