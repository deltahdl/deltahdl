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
  EXPECT_NE(item->unpacked_dims[0], nullptr);
  EXPECT_EQ(item->unpacked_dims[1], nullptr);
}

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
  EXPECT_EQ(item->unpacked_dims[0], nullptr);
  EXPECT_NE(item->unpacked_dims[1], nullptr);
}

// §7.5: any unpacked dimension may be a dynamic array dimension, including the
// element position — a dynamic array whose element is itself a dynamic array
// parses to two unsized (null) unpacked dimensions.
TEST(DynamicArrayParsing, ArrayElementDynamicBothDimsUnsized) {
  auto r = Parse(
      "module t;\n"
      "  int d[][];\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* item = FirstItem(r);
  ASSERT_NE(item, nullptr);
  ASSERT_EQ(item->unpacked_dims.size(), 2u);
  EXPECT_EQ(item->unpacked_dims[0], nullptr);
  EXPECT_EQ(item->unpacked_dims[1], nullptr);
}

}  // namespace
