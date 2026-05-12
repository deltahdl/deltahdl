#include "elaborator/elaborator.h"
#include "elaborator/rtlir.h"
#include "fixture_parser.h"
#include "helpers_parser_verify.h"

using namespace delta;

namespace {

TEST(DynamicArrayParsing, UnsizedDimDynamicArray) {
  auto r = Parse("module m; int d []; endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* item = r.cu->modules[0]->items[0];
  ASSERT_EQ(item->unpacked_dims.size(), 1u);
  EXPECT_EQ(item->unpacked_dims[0], nullptr);
}

TEST(DynamicArrayParsing, PackedElementDynamicArray) {
  auto r = Parse(
      "module t;\n"
      "  bit [3:0] nibble[];\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  auto* item = FirstItem(r);
  ASSERT_NE(item, nullptr);
  EXPECT_EQ(item->name, "nibble");
  ASSERT_EQ(item->unpacked_dims.size(), 1u);
  EXPECT_EQ(item->unpacked_dims[0], nullptr);
}

// §7.5: "Any unpacked dimension in an array declaration may be a dynamic
// dimension." Verify [] is accepted in a non-leftmost position.
TEST(DynamicArrayParsing, InnerDynamicDimension) {
  auto r = Parse(
      "module t;\n"
      "  integer mem[2][];\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* item = FirstItem(r);
  ASSERT_NE(item, nullptr);
  ASSERT_EQ(item->unpacked_dims.size(), 2u);
  EXPECT_NE(item->unpacked_dims[0], nullptr);  // [2]
  EXPECT_EQ(item->unpacked_dims[1], nullptr);  // []
}

// §7.5: Leftmost dynamic dim with inner fixed dim parses cleanly.
TEST(DynamicArrayParsing, LeftmostDynamicWithInnerFixed) {
  auto r = Parse(
      "module t;\n"
      "  integer mem[][2];\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* item = FirstItem(r);
  ASSERT_NE(item, nullptr);
  ASSERT_EQ(item->unpacked_dims.size(), 2u);
  EXPECT_EQ(item->unpacked_dims[0], nullptr);  // []
  EXPECT_NE(item->unpacked_dims[1], nullptr);  // [2]
}

}  // namespace
