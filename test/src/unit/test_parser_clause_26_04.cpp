// §26.4: Using packages in module headers

#include "fixture_parser.h"
#include "helpers_parser_verify.h"

using namespace delta;
namespace {

TEST(ParserSection23, ModuleHeaderMultipleImportsSecond) {
  auto r = Parse(
      "module m import A::*, B::foo; ();\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  auto* mod = r.cu->modules[0];
  ASSERT_GE(mod->items.size(), 2);
  EXPECT_EQ(mod->items[1]->import_item.package_name, "B");
  EXPECT_EQ(mod->items[1]->import_item.item_name, "foo");
}

}  // namespace
