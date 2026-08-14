#include "elaborator/elaborator.h"
#include "elaborator/rtlir.h"
#include "fixture_parser.h"
#include "helpers_parser_verify.h"

using namespace delta;

namespace {

TEST(DeclarationRangeParsing, AssocDimWildcard) {
  auto r = Parse("module m; int aa [*]; endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* item = r.cu->modules[0]->items[0];
  ASSERT_EQ(item->unpacked_dims.size(), 1u);
  ASSERT_NE(item->unpacked_dims[0], nullptr);
  EXPECT_EQ(item->unpacked_dims[0]->text, "*");
}

TEST(AggregateTypeParsing, AssocArrayWildcard) {
  auto r = Parse(
      "module t;\n"
      "  integer aa[*];\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  auto* item = FirstItem(r);
  ASSERT_NE(item, nullptr);
  EXPECT_EQ(item->name, "aa");
  EXPECT_FALSE(item->unpacked_dims.empty());
}

// Covers the `*` branch of Parser::ParseUnpackedDims in
// src/parser/parser_types.cpp, which builds the ExprKind::kIdentifier standing
// for a wildcard index. It assigned no range.start before this commit, and
// src/parser/parser_types.cpp assigned none at any site, so a report standing
// at the dimension printed "<unknown location>" instead of a file, line and
// column. §7.8.1 writes the dimension as `[ * ]`, so the node begins at the
// `*`, at column 11 of line 2.
TEST(DeclarationRangeParsing, AssocWildcardDimStartsAtItsStar) {
  auto r = Parse(
      "module m;\n"
      "  int aa [*];\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* item = FirstItem(r);
  ASSERT_NE(item, nullptr);
  ASSERT_EQ(item->unpacked_dims.size(), 1u);
  auto* dim = item->unpacked_dims[0];
  ASSERT_NE(dim, nullptr);
  EXPECT_EQ(dim->text, "*");
  EXPECT_EQ(dim->range.start.line, 2u);
  EXPECT_EQ(dim->range.start.column, 11u);
}

}  // namespace
