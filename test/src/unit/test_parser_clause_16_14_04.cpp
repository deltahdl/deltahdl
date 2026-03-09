#include "fixture_parser.h"
#include "helpers_parser_verify.h"

using namespace delta;

namespace {

TEST(ParserA210, RestrictProperty_Basic) {
  auto r = Parse(
      "module m;\n"
      "  restrict property (@(posedge clk) a |-> b);\n"
      "endmodule\n");
  EXPECT_FALSE(r.has_errors);
  auto* item = FindItemByKind(r.cu->modules[0]->items,
                              ModuleItemKind::kRestrictProperty);
  ASSERT_NE(item, nullptr);
}

TEST(ParserA210, RestrictProperty_Kind) {
  auto r = Parse(
      "module m;\n"
      "  restrict property (@(posedge clk) req |-> ##[1:3] ack);\n"
      "endmodule\n");
  EXPECT_FALSE(r.has_errors);
  auto* item = FindItemByKind(r.cu->modules[0]->items,
                              ModuleItemKind::kRestrictProperty);
  ASSERT_NE(item, nullptr);
  EXPECT_EQ(item->kind, ModuleItemKind::kRestrictProperty);
  EXPECT_TRUE(item->loc.IsValid());
}

TEST(ParserA210, RestrictProperty_WithDisableIff) {
  EXPECT_TRUE(
      ParseOk("module m;\n"
              "  restrict property (\n"
              "    @(posedge clk) disable iff (rst) a |-> b);\n"
              "endmodule\n"));
}

TEST(ParserA210, RestrictProperty_HasAssertExpr) {
  auto r = Parse(
      "module m;\n"
      "  restrict property (@(posedge clk) a);\n"
      "endmodule\n");
  EXPECT_FALSE(r.has_errors);
  auto* item = FindItemByKind(r.cu->modules[0]->items,
                              ModuleItemKind::kRestrictProperty);
  ASSERT_NE(item, nullptr);
  EXPECT_NE(item->assert_expr, nullptr);
}

TEST(ParserA610, RestrictPropertyModule) {
  auto r = Parse(
      "module m;\n"
      "  restrict property (clk);\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* item = FindItemByKind(r, ModuleItemKind::kRestrictProperty);
  ASSERT_NE(item, nullptr);
}

}  // namespace
