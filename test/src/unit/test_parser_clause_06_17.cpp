#include "elaborator/type_eval.h"
#include "fixture_parser.h"
#include "helpers_parser_verify.h"
#include "parser/ast.h"

using namespace delta;
namespace {

TEST(DataTypeParsing, EventVarDecl) {
  auto r = Parse(
      "module t;\n"
      "  event done;\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* item = FirstItem(r);
  ASSERT_NE(item, nullptr);
  EXPECT_EQ(item->kind, ModuleItemKind::kVarDecl);
  EXPECT_EQ(item->data_type.kind, DataTypeKind::kEvent);
  EXPECT_FALSE(item->data_type.is_net);
  EXPECT_EQ(item->name, "done");
}

TEST(DataTypeParsing, EventNotIntegral) {
  EXPECT_FALSE(IsIntegralType(DataTypeKind::kEvent));
}

TEST(DataTypeParsing, EventAssignNull) {
  auto r = Parse(
      "module t;\n"
      "  event empty = null;\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* item = FirstItem(r);
  ASSERT_NE(item, nullptr);
  EXPECT_EQ(item->data_type.kind, DataTypeKind::kEvent);
}

TEST(DataTypeParsing, EventInitFromAnotherEvent) {
  auto r = Parse(
      "module t;\n"
      "  event done;\n"
      "  event done_too = done;\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* mod = r.cu->modules[0];
  ASSERT_GE(mod->items.size(), 2u);
  auto* aliased = mod->items[1];
  EXPECT_EQ(aliased->kind, ModuleItemKind::kVarDecl);
  EXPECT_EQ(aliased->data_type.kind, DataTypeKind::kEvent);
  EXPECT_EQ(aliased->name, "done_too");
  ASSERT_NE(aliased->init_expr, nullptr);
  EXPECT_EQ(aliased->init_expr->kind, ExprKind::kIdentifier);
  EXPECT_EQ(aliased->init_expr->text, "done");
}

}  // namespace
