#include "fixture_parser.h"
#include "helpers_parser_verify.h"

using namespace delta;

namespace {

TEST(UnionDeclarationPreprocessor, UnpackedUnionForwardsThroughPreprocessor) {
  auto r = ParseWithPreprocessor(
      "module t;\n"
      "  union { int i; shortreal f; } u;\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  auto* item = FirstItem(r);
  ASSERT_NE(item, nullptr);
  EXPECT_EQ(item->data_type.kind, DataTypeKind::kUnion);
  EXPECT_FALSE(item->data_type.is_packed);
  EXPECT_FALSE(item->data_type.is_tagged);
  EXPECT_FALSE(item->data_type.is_soft);
  EXPECT_EQ(item->data_type.struct_members.size(), 2u);
}

TEST(UnionDeclarationPreprocessor, TaggedUnionForwardsThroughPreprocessor) {
  auto r = ParseWithPreprocessor(
      "module t;\n"
      "  union tagged { void Invalid; int Valid; } u;\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  auto* item = FirstItem(r);
  ASSERT_NE(item, nullptr);
  EXPECT_EQ(item->data_type.kind, DataTypeKind::kUnion);
  EXPECT_TRUE(item->data_type.is_tagged);
  EXPECT_EQ(item->data_type.struct_members[0].type_kind, DataTypeKind::kVoid);
}

TEST(UnionDeclarationPreprocessor, MacroExpandsToUnionDeclaration) {
  auto r = ParseWithPreprocessor(
      "`define NUM union { int i; shortreal f; }\n"
      "module t;\n"
      "  `NUM n;\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  auto* item = FirstItem(r);
  ASSERT_NE(item, nullptr);
  EXPECT_EQ(item->data_type.kind, DataTypeKind::kUnion);
  EXPECT_EQ(item->data_type.struct_members.size(), 2u);
}

}  // namespace
