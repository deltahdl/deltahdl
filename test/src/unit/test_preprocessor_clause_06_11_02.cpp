// §6.11.2: 2-state (two-value) and 4-state (four-value) data types

#include "fixture_parser.h"
#include "elaborator/type_eval.h"

using namespace delta;

static ModuleItem* FirstItem(ParseResult& r) {
  if (!r.cu || r.cu->modules.empty()) return nullptr;
  auto& items = r.cu->modules[0]->items;
  return items.empty() ? nullptr : items[0];
}

namespace {

TEST(ParserSection6, ValueSet_2StateBitDecl) {
  // §6.3: bit is a 2-state type (only 0 and 1).
  auto r = ParseWithPreprocessor(
      "module t;\n"
      "  bit [7:0] val;\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  auto* item = FirstItem(r);
  ASSERT_NE(item, nullptr);
  EXPECT_EQ(item->data_type.kind, DataTypeKind::kBit);
  EXPECT_FALSE(Is4stateType(DataTypeKind::kBit));
}

}  // namespace
