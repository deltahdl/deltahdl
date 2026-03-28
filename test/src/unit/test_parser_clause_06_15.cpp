#include "fixture_parser.h"

using namespace delta;
namespace {

TEST(DataTypeParsing, ClassVariableDecl) {
  auto r = Parse(
      "class Packet;\n"
      "  int payload;\n"
      "endclass\n"
      "module m;\n"
      "  Packet pkt;\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto& items = r.cu->modules[0]->items;
  ModuleItem* var_item = nullptr;
  for (auto* it : items) {
    if (it->kind == ModuleItemKind::kVarDecl && it->name == "pkt") {
      var_item = it;
      break;
    }
  }
  ASSERT_NE(var_item, nullptr);
  EXPECT_EQ(var_item->data_type.kind, DataTypeKind::kNamed);
  EXPECT_EQ(var_item->data_type.type_name, "Packet");
}

}  // namespace
