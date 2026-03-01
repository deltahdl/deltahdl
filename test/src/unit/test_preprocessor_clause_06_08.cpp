// §6.8: on variable initialization). This is roughly equivalent to a C automatic variable.

#include "fixture_parser.h"
#include "elaborator/type_eval.h"

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

}  // namespace
