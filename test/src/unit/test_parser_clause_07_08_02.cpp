#include "fixture_parser.h"
#include "helpers_parser_verify.h"

using namespace delta;

namespace {

TEST(StringIndexAssocArrayParsing, VarDeclAssignmentAssocArray) {
  auto r = Parse("module m; int aa [string]; endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* item = r.cu->modules[0]->items[0];
  EXPECT_EQ(item->kind, ModuleItemKind::kVarDecl);
  EXPECT_EQ(item->name, "aa");
}

TEST(StringIndexAssocArrayParsing, AssocArrayStringIndex_DimExpr) {
  auto r = Parse(
      "module t;\n"
      "  int scores[string];\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  auto* item = FirstItem(r);
  ASSERT_NE(item, nullptr);
  ASSERT_EQ(item->unpacked_dims.size(), 1u);
  EXPECT_EQ(item->unpacked_dims[0]->kind, ExprKind::kIdentifier);
  EXPECT_EQ(item->unpacked_dims[0]->text, "string");
}

}  // namespace
