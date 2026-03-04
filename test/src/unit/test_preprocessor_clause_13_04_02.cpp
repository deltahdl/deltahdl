// §13.4.2: Static and automatic functions

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
// §6.11.1: Integral types — automatic variables in functions
// =========================================================================
TEST(ParserSection6, AutomaticFunctionLocalVar) {
  // §6.11.1: Automatic function has automatic local variables.
  auto r = ParseWithPreprocessor(
      "module t;\n"
      "  function automatic int factorial(int n);\n"
      "    if (n <= 1) return 1;\n"
      "    return n * factorial(n - 1);\n"
      "  endfunction\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  auto* item = FirstItem(r);
  ASSERT_NE(item, nullptr);
  EXPECT_EQ(item->kind, ModuleItemKind::kFunctionDecl);
  EXPECT_TRUE(item->is_automatic);
}

}  // namespace
