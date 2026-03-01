// §6.3.1: Logic values

#include "fixture_parser.h"
#include "elaborator/type_eval.h"

using namespace delta;

static ModuleItem* FirstItem(ParseResult& r) {
  if (!r.cu || r.cu->modules.empty()) return nullptr;
  auto& items = r.cu->modules[0]->items;
  return items.empty() ? nullptr : items[0];
}

namespace {

// =========================================================================
// §6.3: Value set — 4-state vs 2-state data types
// =========================================================================
TEST(ParserSection6, ValueSet_4StateLogicDecl) {
  // §6.3: logic is the basic 4-state data type.
  auto r = ParseWithPreprocessor(
      "module t;\n"
      "  logic [3:0] val;\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  auto* item = FirstItem(r);
  ASSERT_NE(item, nullptr);
  EXPECT_EQ(item->data_type.kind, DataTypeKind::kLogic);
  EXPECT_TRUE(Is4stateType(DataTypeKind::kLogic));
}

}  // namespace
