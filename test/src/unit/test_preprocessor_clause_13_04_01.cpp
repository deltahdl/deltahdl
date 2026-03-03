// §13.4.1: Return values and void functions

#include "fixture_parser.h"
#include "elaborator/type_eval.h"

using namespace delta;

static ModuleItem* FirstItem(ParseResult& r) {
  if (!r.cu || r.cu->modules.empty()) return nullptr;
  auto& items = r.cu->modules[0]->items;
  return items.empty() ? nullptr : items[0];
}

namespace {

TEST(ParserSection6, AutomaticFunctionReturnType) {
  // §6.11.1: Function return type is an integral type.
  auto r = ParseWithPreprocessor(
      "module t;\n"
      "  function automatic int get_value();\n"
      "    return 42;\n"
      "  endfunction\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  auto* item = FirstItem(r);
  ASSERT_NE(item, nullptr);
  EXPECT_EQ(item->return_type.kind, DataTypeKind::kInt);
}

}  // namespace
