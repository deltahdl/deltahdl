#include "fixture_parser.h"

using namespace delta;

namespace {

TEST(UserDefinedTypeAssocArrayParsing, TypedefIndexParsed) {
  auto r = Parse(
      "module t;\n"
      "  typedef bit [3:0] nibble_t;\n"
      "  int aa[nibble_t];\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
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
  EXPECT_EQ(var_item->unpacked_dims[0]->text, "nibble_t");
}

TEST(UserDefinedTypeAssocArrayParsing, EnumTypedefIndexParsed) {
  auto r = Parse(
      "module t;\n"
      "  typedef enum {A, B, C} abc_t;\n"
      "  int aa[abc_t];\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
}

TEST(UserDefinedTypeAssocArrayParsing, StructTypedefIndexParsed) {
  auto r = Parse(
      "module t;\n"
      "  typedef struct {byte b; int i;} my_struct_t;\n"
      "  int aa[my_struct_t];\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
}

}  // namespace
