#include "fixture_parser.h"
#include "helpers_parser_verify.h"

using namespace delta;
namespace {

TEST(Parser, NettypeUsedInDecl) {
  auto r = Parse(
      "module t;\n"
      "  nettype logic [7:0] mynet;\n"
      "  mynet x;\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  ASSERT_GE(r.cu->modules[0]->items.size(), 2u);
  auto* item = r.cu->modules[0]->items[1];
  EXPECT_EQ(item->kind, ModuleItemKind::kVarDecl);
  EXPECT_EQ(item->name, "x");
}

TEST(ParserSection6, Sec6_6_7_NettypeUsedForNetDecl) {
  EXPECT_TRUE(
      ParseOk("module m;\n"
              "  typedef struct { real field1; bit field2; } T;\n"
              "  nettype T wT;\n"
              "  wT my_signal;\n"
              "endmodule\n"));
}

}
