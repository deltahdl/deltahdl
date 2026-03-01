// §30.4.7.1: Unknown polarity

#include "fixture_parser.h"
#include "helpers_parser_verify.h"

using namespace delta;

ModuleItem* FindSpecifyBlock(const std::vector<ModuleItem*>& items) {
  for (auto* item : items) {
    if (item->kind == ModuleItemKind::kSpecifyBlock) return item;
  }
  return nullptr;
}

SpecifyItem* GetSolePathItem(ParseResult& r) {
  if (!r.cu || r.cu->modules.empty()) return nullptr;
  auto* spec = FindSpecifyBlock(r.cu->modules[0]->items);
  if (!spec || spec->specify_items.empty()) return nullptr;
  return spec->specify_items[0];
}

namespace {

// ( input => output ) — no polarity (default)
TEST(ParserA702, ParallelPathNoPolarity) {
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
  EXPECT_EQ(si->path.polarity, SpecifyPolarity::kNone);
}

// ( inputs *> outputs ) — no polarity (default)
TEST(ParserA702, FullPathNoPolarity) {
  auto r = Parse(
      "module m;\n"
      "  specify\n"
      "    (a, b *> c) = 5;\n"
      "  endspecify\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* si = GetSolePathItem(r);
  ASSERT_NE(si, nullptr);
  EXPECT_EQ(si->path.path_kind, SpecifyPathKind::kFull);
  EXPECT_EQ(si->path.polarity, SpecifyPolarity::kNone);
}

}  // namespace
