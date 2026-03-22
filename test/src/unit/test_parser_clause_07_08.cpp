#include "fixture_parser.h"
#include "helpers_parser_verify.h"

using namespace delta;

namespace {

// §7.8: General associative array declaration syntax parses.
TEST(AssocArrayParsing, Declaration) {
  auto r = Parse(
      "module t;\n"
      "  int aa[int];\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* item = FirstItem(r);
  ASSERT_NE(item, nullptr);
  EXPECT_EQ(item->name, "aa");
  ASSERT_EQ(item->unpacked_dims.size(), 1u);
  ASSERT_NE(item->unpacked_dims[0], nullptr);
}

// §7.8: Element type can be any data type.
TEST(AssocArrayParsing, VectorElementType) {
  auto r = Parse(
      "module t;\n"
      "  logic [15:0] mem[int];\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* item = FirstItem(r);
  ASSERT_NE(item, nullptr);
  EXPECT_EQ(item->data_type.kind, DataTypeKind::kLogic);
}

// §7.8: Multiple associative arrays in one module.
TEST(AssocArrayParsing, MultipleDeclarations) {
  auto r = Parse(
      "module t;\n"
      "  int a[int];\n"
      "  string b[string];\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  ASSERT_GE(r.cu->modules[0]->items.size(), 2u);
}

}  // namespace
