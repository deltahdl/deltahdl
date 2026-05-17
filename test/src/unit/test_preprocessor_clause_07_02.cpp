#include "fixture_parser.h"
#include "helpers_parser_verify.h"

using namespace delta;

namespace {

// §7.2 does not introduce any preprocessor directives — the preprocessor
// only needs to forward struct/union declarations to the parser unchanged.
// These tests pin that contract: structure source text survives the
// preprocessor and the parser still recognises it as a struct/union.

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

// §7.2: a macro that expands to a struct declaration must reach the parser
// as the equivalent literal text — the preprocessor cannot rewrite or drop
// the struct/union keyword inside the expansion.
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
