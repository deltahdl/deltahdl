#include "fixture_parser.h"

using namespace delta;

namespace {

TEST(ParserA84, ConstantPrimaryEnumIdentifier) {
  auto r = Parse(
      "module m;\n"
      "  typedef enum {RED, GREEN, BLUE} color_t;\n"
      "  parameter color_t C = RED;\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
}

// §6.19.3: Enum used as parameter default value.
TEST(ParserSection6, EnumAsParameterValue) {
  auto r = Parse(
      "module m;\n"
      "  typedef enum {RED, GREEN, BLUE} color_t;\n"
      "  parameter color_t DEFAULT_COLOR = GREEN;\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
}

// §6.19.3: Multiple variables of same enum type.
TEST(ParserSection6, EnumMultipleVars) {
  auto r = Parse(
      "module m;\n"
      "  typedef enum { red, green, blue, yellow, white, black } Colors;\n"
      "  Colors c1, c2;\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
}

}  // namespace
