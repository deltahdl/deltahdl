#include "fixture_parser.h"
#include "helpers_parser_verify.h"

using namespace delta;

namespace {

TEST(ParserA704, PathDelayValueBare) {
  auto r = Parse(
      "module m;\n"
      "  specify\n"
      "    (a => b) = 5;\n"
      "  endspecify\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* si = GetSolePathItem(r);
  ASSERT_NE(si, nullptr);
  ASSERT_EQ(si->path.delays.size(), 1u);
}

TEST(ParserA704, PathDelayValueParenthesized) {
  auto r = Parse(
      "module m;\n"
      "  specify\n"
      "    (a => b) = (5);\n"
      "  endspecify\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* si = GetSolePathItem(r);
  ASSERT_NE(si, nullptr);
  ASSERT_EQ(si->path.delays.size(), 1u);
}

TEST(ParserA704, PathDelayWithSpecparam) {
  auto r = Parse(
      "module m;\n"
      "  specify\n"
      "    specparam tDelay = 10;\n"
      "    (a => b) = tDelay;\n"
      "  endspecify\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* spec = FindSpecifyBlock(r.cu->modules[0]->items);
  ASSERT_NE(spec, nullptr);
  ASSERT_GE(spec->specify_items.size(), 2u);
  auto* path_item = spec->specify_items[1];
  EXPECT_EQ(path_item->kind, SpecifyItemKind::kPathDecl);
  ASSERT_EQ(path_item->path.delays.size(), 1u);
}

TEST(ParserAnnexA, A7SpecparamInSpecify) {
  auto r = Parse(
      "module m;\n"
      "  specify\n"
      "    specparam tRISE = 100;\n"
      "    (a => b) = tRISE;\n"
      "  endspecify\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
}

}
