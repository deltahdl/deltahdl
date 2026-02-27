// §7.5.1: New[ ]

#include "fixture_parser.h"

using namespace delta;

namespace {

// --- dynamic_array_new ---
// new [ expression ] [ ( expression ) ]
TEST(ParserA24, DynamicArrayNewSize) {
  auto r = Parse(
      "module m;\n"
      "  int d[];\n"
      "  initial d = new[10];\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
}

TEST(ParserA24, DynamicArrayNewSizeAndInit) {
  auto r = Parse(
      "module m;\n"
      "  int d[];\n"
      "  int src [10];\n"
      "  initial d = new[10](src);\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
}

TEST(ParserA24, DynamicArrayDeclWithNew) {
  auto r = Parse(
      "module m;\n"
      "  int d[] = new[5];\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
}

}  // namespace
