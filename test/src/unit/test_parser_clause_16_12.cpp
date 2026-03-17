#include "fixture_parser.h"

using namespace delta;

namespace {

TEST(AssertionSemanticsParsing, PropertyDecl) {
  auto r = Parse(
      "module m;\n"
      "  property p1;\n"
      "    @(posedge clk) a |-> ##1 b;\n"
      "  endproperty\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  ASSERT_EQ(r.cu->modules.size(), 1u);
  bool found = false;
  for (auto* item : r.cu->modules[0]->items) {
    if (item->kind == ModuleItemKind::kPropertyDecl) {
      found = true;
      EXPECT_EQ(item->name, "p1");
    }
  }
  EXPECT_TRUE(found);
}

}  // namespace
