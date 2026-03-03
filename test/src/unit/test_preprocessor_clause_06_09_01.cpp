// §6.9.1: Specifying vectors

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
// §6.9: Vector declarations
// =========================================================================
TEST(ParserSection6, VectorBigEndian) {
  // §6.9: Vector [msb:lsb] with msb > lsb (big-endian).
  auto r = ParseWithPreprocessor(
      "module t;\n"
      "  logic [31:0] wide;\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  auto* item = FirstItem(r);
  ASSERT_NE(item, nullptr);
  ASSERT_NE(item->data_type.packed_dim_left, nullptr);
  ASSERT_NE(item->data_type.packed_dim_right, nullptr);
  EXPECT_EQ(item->data_type.packed_dim_left->int_val, 31u);
  EXPECT_EQ(item->data_type.packed_dim_right->int_val, 0u);
}

}  // namespace
