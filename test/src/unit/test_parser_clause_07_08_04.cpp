// §7.8.4: Integral index

#include "elaborator/elaborator.h"
#include "elaborator/rtlir.h"
#include "fixture_parser.h"
#include "helpers_parser_verify.h"

using namespace delta;

namespace {

TEST(ParserA25, AssocDimIntType) {
  auto r = Parse("module m; logic [7:0] aa [int]; endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto *item = r.cu->modules[0]->items[0];
  ASSERT_EQ(item->unpacked_dims.size(), 1u);
  ASSERT_NE(item->unpacked_dims[0], nullptr);
  EXPECT_EQ(item->unpacked_dims[0]->text, "int");
}

TEST(ParserA25, AssocDimByteType) {
  auto r = Parse("module m; int aa [byte]; endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto *item = r.cu->modules[0]->items[0];
  ASSERT_EQ(item->unpacked_dims.size(), 1u);
  EXPECT_EQ(item->unpacked_dims[0]->text, "byte");
}
TEST(ParserSection7, AssocArrayIntIndex) {
  auto r = Parse("module t;\n"
                 "  byte lookup[int];\n"
                 "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  auto *item = FirstItem(r);
  ASSERT_NE(item, nullptr);
  EXPECT_EQ(item->name, "lookup");
  ASSERT_EQ(item->unpacked_dims.size(), 1u);
  ASSERT_NE(item->unpacked_dims[0], nullptr);
}

TEST(ParserSection7, AssocArrayIntegerIndex) {
  auto r = Parse("module t;\n"
                 "  logic [7:0] cache[integer];\n"
                 "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  auto *item = FirstItem(r);
  ASSERT_NE(item, nullptr);
  EXPECT_EQ(item->name, "cache");
  ASSERT_EQ(item->unpacked_dims.size(), 1u);
}

TEST(ParserSection7, AssocArrayIntegerIndex_DimExpr) {
  auto r = Parse("module t;\n"
                 "  logic [7:0] cache[integer];\n"
                 "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  auto *item = FirstItem(r);
  ASSERT_NE(item, nullptr);
  ASSERT_EQ(item->unpacked_dims.size(), 1u);
  ASSERT_NE(item->unpacked_dims[0], nullptr);
  EXPECT_EQ(item->unpacked_dims[0]->text, "integer");
}
// --- Test helpers ---
TEST(ParserSection7, AssociativeArrayIntIndex) {
  auto r = Parse("module t;\n"
                 "  string names[int];\n"
                 "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  auto *item = FirstItem(r);
  ASSERT_NE(item, nullptr);
  EXPECT_EQ(item->name, "names");
}

} // namespace
