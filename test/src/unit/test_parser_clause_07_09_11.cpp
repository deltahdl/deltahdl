#include "fixture_parser.h"

using namespace delta;
namespace {

// §7.9.11: Assoc array literal with default.
TEST(ParserSection7, AssocArrayLiteralWithDefault) {
  auto r = Parse(
      "module t;\n"
      "  string words[int] = '{default: \"hello\"};\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
}

// §7.9.11: Assoc array literal with key-value pairs.
TEST(ParserSection7, AssocArrayLiteralKeyValue) {
  auto r = Parse(
      "module t;\n"
      "  integer tab[string] = '{\"Peter\":20, \"Paul\":22, default:-1};\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
}

}  // namespace
