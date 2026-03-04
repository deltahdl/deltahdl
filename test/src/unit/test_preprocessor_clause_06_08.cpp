// §6.8: on variable initialization). This is roughly equivalent to a C
// automatic variable.

#include "elaborator/type_eval.h"
#include "fixture_parser.h"

using namespace delta;

static ModuleItem* FirstItem(ParseResult& r) {
  if (!r.cu || r.cu->modules.empty()) return nullptr;
  auto& items = r.cu->modules[0]->items;
  return items.empty() ? nullptr : items[0];
}

namespace {

TEST(ParserSection6, VarBareNoType) {
  // §6.8: "var v;" — no type at all implies logic.
  auto r = ParseWithPreprocessor(
      "module t;\n"
      "  var v;\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  auto* item = FirstItem(r);
  ASSERT_NE(item, nullptr);
  EXPECT_EQ(item->name, "v");
}

TEST(ParserSection6, VarWithInitializer) {
  // §6.8: Variable with initializer "int i = 0;"
  auto r = ParseWithPreprocessor(
      "module t;\n"
      "  int i = 0;\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  auto* item = FirstItem(r);
  ASSERT_NE(item, nullptr);
  EXPECT_EQ(item->data_type.kind, DataTypeKind::kInt);
  EXPECT_EQ(item->name, "i");
  EXPECT_NE(item->init_expr, nullptr);
}

TEST(ParserSection6, MultipleVarDeclsSameStmt) {
  // §6.8: "shortint s1, s2[0:9];" — multiple instances in one decl.
  auto r = ParseWithPreprocessor(
      "module t;\n"
      "  shortint s1, s2;\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  ASSERT_GE(r.cu->modules[0]->items.size(), 2u);
  EXPECT_EQ(r.cu->modules[0]->items[0]->name, "s1");
  EXPECT_EQ(r.cu->modules[0]->items[1]->name, "s2");
}

}  // namespace
