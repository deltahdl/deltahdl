#include "fixture_parser.h"

using namespace delta;

namespace {

TEST(PrimaryParsing, ConstantPrimaryEnumIdentifier) {
  auto r = Parse(
      "module m;\n"
      "  typedef enum {RED, GREEN, BLUE} color_t;\n"
      "  parameter color_t C = RED;\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
}

TEST(DataTypeParsing, EnumAsParameterValue) {
  auto r = Parse(
      "module m;\n"
      "  typedef enum {RED, GREEN, BLUE} color_t;\n"
      "  parameter color_t DEFAULT_COLOR = GREEN;\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
}

TEST(DataTypeParsing, EnumMultipleVars) {
  auto r = Parse(
      "module m;\n"
      "  typedef enum { red, green, blue, yellow, white, black } Colors;\n"
      "  Colors c1, c2;\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
}

}  // namespace
