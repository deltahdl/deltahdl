#include "fixture_parser.h"

using namespace delta;

namespace {

// §7.8.3: Associative array with class index parses correctly.
TEST(ParserSection7, AssocArrayClassIndex) {
  auto r = Parse(
      "module t;\n"
      "  class Foo;\n"
      "    int id;\n"
      "  endclass\n"
      "  int data[Foo];\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
}

// §7.8.3: Class index dimension is parsed as identifier with class name.
TEST(ParserSection7, AssocArrayClassIndex_DimExpr) {
  auto r = Parse(
      "module t;\n"
      "  class MyClass;\n"
      "    int x;\n"
      "  endclass\n"
      "  int aa[MyClass];\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  // The variable decl is the second item (after the class decl).
  auto& items = r.cu->modules[0]->items;
  ModuleItem* var_item = nullptr;
  for (auto* item : items) {
    if (item->kind == ModuleItemKind::kVarDecl && item->name == "aa") {
      var_item = item;
      break;
    }
  }
  ASSERT_NE(var_item, nullptr);
  ASSERT_EQ(var_item->unpacked_dims.size(), 1u);
  ASSERT_NE(var_item->unpacked_dims[0], nullptr);
  EXPECT_EQ(var_item->unpacked_dims[0]->kind, ExprKind::kIdentifier);
  EXPECT_EQ(var_item->unpacked_dims[0]->text, "MyClass");
}

// §7.8.3: Multiple variables with the same class index type.
TEST(ParserSection7, AssocArrayClassIndex_MultipleVars) {
  auto r = Parse(
      "module t;\n"
      "  class Key;\n"
      "    int id;\n"
      "  endclass\n"
      "  int aa[Key];\n"
      "  int bb[Key];\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
}

// §7.8.3: Different element types with class index.
TEST(ParserSection7, AssocArrayClassIndex_DifferentElemTypes) {
  auto r = Parse(
      "module t;\n"
      "  class Idx;\n"
      "    int x;\n"
      "  endclass\n"
      "  logic [7:0] data[Idx];\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
}

}  // namespace
