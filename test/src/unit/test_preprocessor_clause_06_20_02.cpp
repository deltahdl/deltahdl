// §6.20.2: Value parameters

#include "elaborator/type_eval.h"
#include "fixture_parser.h"

using namespace delta;

static ModuleItem* FirstItem(ParseResult& r) {
  if (!r.cu || r.cu->modules.empty()) return nullptr;
  auto& items = r.cu->modules[0]->items;
  return items.empty() ? nullptr : items[0];
}

namespace {

// =========================================================================
// §6.20: Constants — parameter and localparam
// =========================================================================
TEST(ParserSection6, ParameterWithExplicitType) {
  // §6.20: parameter with explicit type.
  auto r = ParseWithPreprocessor(
      "module t;\n"
      "  parameter int WIDTH = 8;\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  auto* item = FirstItem(r);
  ASSERT_NE(item, nullptr);
  EXPECT_EQ(item->kind, ModuleItemKind::kParamDecl);
  ASSERT_NE(item->init_expr, nullptr);
}

}  // namespace
