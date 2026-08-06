#include "fixture_parser.h"
#include "helpers_parser_verify.h"

using namespace delta;

namespace {

TEST(StructDeclarationPreprocessor, StructForwardsThroughPreprocessor) {
  auto r = ParseWithPreprocessor(
      "module t;\n"
      "  struct { int x; int y; } point;\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  auto* item = FirstItem(r);
  ASSERT_NE(item, nullptr);
  EXPECT_EQ(item->kind, ModuleItemKind::kVarDecl);
  EXPECT_EQ(item->data_type.kind, DataTypeKind::kStruct);
  EXPECT_EQ(item->name, "point");
  EXPECT_EQ(item->data_type.struct_members.size(), 2u);
}

TEST(StructDeclarationPreprocessor, UnionForwardsThroughPreprocessor) {
  auto r = ParseWithPreprocessor(
      "module t;\n"
      "  union packed { logic [7:0] a; logic [7:0] b; } u;\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  auto* item = FirstItem(r);
  ASSERT_NE(item, nullptr);
  EXPECT_EQ(item->data_type.kind, DataTypeKind::kUnion);
  EXPECT_TRUE(item->data_type.is_packed);
}

TEST(StructDeclarationPreprocessor, MacroExpandsToStructDeclaration) {
  auto r = ParseWithPreprocessor(
      "`define POINT struct { int x; int y; }\n"
      "module t;\n"
      "  `POINT p;\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  auto* item = FirstItem(r);
  ASSERT_NE(item, nullptr);
  EXPECT_EQ(item->data_type.kind, DataTypeKind::kStruct);
  EXPECT_EQ(item->data_type.struct_members.size(), 2u);
}

}  // namespace
