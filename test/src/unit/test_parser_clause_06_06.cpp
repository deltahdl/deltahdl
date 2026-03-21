#include "fixture_parser.h"

using namespace delta;

namespace {

TEST(FormalSyntaxParsing, NetDeclTriWandWor) {
  auto r = Parse("module m; tri t; wand wa; wor wo; endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  EXPECT_EQ(r.cu->modules[0]->items.size(), 3u);
}
TEST(DataTypeParsing, AllBuiltinNetTypes) {
  auto r = Parse(
      "module t;\n"
      "  wire w;\n"
      "  tri t;\n"
      "  wand wa;\n"
      "  wor wo;\n"
      "  triand ta;\n"
      "  trior to_;\n"
      "  tri0 t0;\n"
      "  tri1 t1;\n"
      "  trireg tr;\n"
      "  supply0 s0;\n"
      "  supply1 s1;\n"
      "  uwire uw;\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto& items = r.cu->modules[0]->items;
  ASSERT_GE(items.size(), 12u);
  for (size_t i = 0; i < 12u; ++i) {
    EXPECT_EQ(items[i]->kind, ModuleItemKind::kNetDecl) << "item " << i;
    EXPECT_TRUE(items[i]->data_type.is_net) << "item " << i;
  }
}

}  // namespace
