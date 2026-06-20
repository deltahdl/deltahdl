#include "fixture_parser.h"
#include "helpers_parser_verify.h"

using namespace delta;

namespace {

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

TEST(AssocArrayParsing, InlineStructTypeAsIndexRejected) {
  auto r = Parse(
      "module t;\n"
      "  int aa [ struct { int x; } ];\n"
      "endmodule\n");
  EXPECT_TRUE(r.has_errors);
}

}  // namespace
