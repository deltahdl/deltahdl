#include "fixture_parser.h"
#include "helpers_parser_verify.h"

using namespace delta;

namespace {

// Annex D.6: $list may be invoked with no argument, parsing as an ordinary
// system task call.
TEST(OptionalListParserParsing, NoArgument) {
  auto r = Parse(
      "module m;\n"
      "  initial $list;\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
}

// Annex D.6: the optional argument is a hierarchical name naming a specific
// scope to list.
TEST(OptionalListParserParsing, HierarchicalArgument) {
  auto r = Parse(
      "module m;\n"
      "  initial $list(m.blk);\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
}

// Annex D.6: the hierarchical-name argument may descend several levels, so a
// dotted name reaching a block nested inside another named block parses with no
// diagnostics.
TEST(OptionalListParserParsing, MultiLevelHierarchicalArgument) {
  EXPECT_TRUE(ParseOk(
      "module m;\n"
      "  initial $list(m.outer.inner);\n"
      "endmodule\n"));
}

// Annex D.6: both forms (bare and parenthesized) are accepted by the parser
// without producing diagnostics.
TEST(OptionalListParserParsing, BareFormParsesWithoutError) {
  EXPECT_TRUE(ParseOk(
      "module m;\n"
      "  initial $list;\n"
      "endmodule\n"));
}

}  // namespace
