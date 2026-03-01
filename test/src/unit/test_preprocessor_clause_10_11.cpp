// §10.11: Net aliasing

#include "fixture_parser.h"

using namespace delta;

namespace {

// net_alias: alias net1 = net2 = net3;
TEST(SourceText, NetAlias) {
  auto r = ParseWithPreprocessor(
      "module m;\n"
      "  wire a, b, c;\n"
      "  alias a = b = c;\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto& items = r.cu->modules[0]->items;
  // 3 wire decls + 1 alias
  auto* alias_item = items.back();
  EXPECT_EQ(alias_item->kind, ModuleItemKind::kAlias);
  EXPECT_EQ(alias_item->alias_nets.size(), 3u);
}

}  // namespace
