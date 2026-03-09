#include "fixture_parser.h"
#include "helpers_parser_verify.h"

using namespace delta;
SpecifyItem* GetSolePathItem(ParseResult& r) {
  if (!r.cu || r.cu->modules.empty()) return nullptr;
  auto* spec = FindSpecifyBlock(r.cu->modules[0]->items);
  if (!spec || spec->specify_items.empty()) return nullptr;
  return spec->specify_items[0];
}

namespace {

TEST(ParserA702, ParallelPathNegativePolarity) {
  auto r = Parse(
      "module m;\n"
      "  specify\n"
      "    (a - => b) = 5;\n"
      "  endspecify\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* si = GetSolePathItem(r);
  ASSERT_NE(si, nullptr);
  EXPECT_EQ(si->path.path_kind, SpecifyPathKind::kParallel);
  EXPECT_EQ(si->path.polarity, SpecifyPolarity::kNegative);
}

TEST(ParserA702, FullPathNegativePolarity) {
  auto r = Parse(
      "module m;\n"
      "  specify\n"
      "    (a - *> b) = 5;\n"
      "  endspecify\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* si = GetSolePathItem(r);
  ASSERT_NE(si, nullptr);
  EXPECT_EQ(si->path.path_kind, SpecifyPathKind::kFull);
  EXPECT_EQ(si->path.polarity, SpecifyPolarity::kNegative);
}

}  // namespace
