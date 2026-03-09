#include "elaborator/type_eval.h"
#include "fixture_parser.h"
#include "helpers_parser_verify.h"
#include "parser/ast.h"

using namespace delta;
namespace {

TEST(Parser, EventDeclaration) {
  auto r = Parse(
      "module t;\n"
      "  event ev;\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  auto* item = r.cu->modules[0]->items[0];
  EXPECT_EQ(item->kind, ModuleItemKind::kVarDecl);
  EXPECT_EQ(item->data_type.kind, DataTypeKind::kEvent);
  EXPECT_EQ(item->name, "ev");
}

TEST(ParserA221, DataTypeEvent) {
  auto r = Parse("module m; event ev; endmodule");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  EXPECT_EQ(r.cu->modules[0]->items[0]->data_type.kind, DataTypeKind::kEvent);
}

TEST(ParserSection6, Sec6_5_EventVarDecl) {
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

TEST(ParserSection6, EventVarDecl) {
  auto r = Parse(
      "module t;\n"
      "  event e;\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  auto* item = FirstItem(r);
  ASSERT_NE(item, nullptr);
  EXPECT_EQ(item->data_type.kind, DataTypeKind::kEvent);
}

TEST(ParserSection6, EventTypeWidthZero) {
  DataType dt;
  dt.kind = DataTypeKind::kEvent;
  EXPECT_EQ(EvalTypeWidth(dt), 0u);
}

TEST(ParserSection6, EventNotIntegral) {
  EXPECT_FALSE(IsIntegralType(DataTypeKind::kEvent));
}

TEST(ParserSection6, EventNot4State) {
  EXPECT_FALSE(Is4stateType(DataTypeKind::kEvent));
}

TEST(ParserSection6, EventAssignEvent) {
  auto r = Parse(
      "module t;\n"
      "  event done;\n"
      "  event done_too = done;\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* item0 = r.cu->modules[0]->items[0];
  auto* item1 = r.cu->modules[0]->items[1];
  EXPECT_EQ(item0->data_type.kind, DataTypeKind::kEvent);
  EXPECT_EQ(item1->data_type.kind, DataTypeKind::kEvent);
  EXPECT_NE(item1->init_expr, nullptr);
}

TEST(ParserSection6, EventAssignNull) {
  auto r = Parse(
      "module t;\n"
      "  event empty = null;\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* item = FirstItem(r);
  EXPECT_EQ(item->data_type.kind, DataTypeKind::kEvent);
  EXPECT_NE(item->init_expr, nullptr);
}

}  // namespace
