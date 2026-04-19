#include "fixture_parser.h"
#include "fixture_specify.h"
#include "helpers_parser_verify.h"

using namespace delta;

namespace {

// --- Error conditions ---

TEST(SpecifyPathParsing, ErrorPathDeclMissingSemicolon) {
  auto r = Parse(
      "module m;\n"
      "  specify\n"
      "    (a => b) = 5\n"
      "  endspecify\n"
      "endmodule\n");
  EXPECT_TRUE(r.has_errors);
}

TEST(SpecifyPathParsing, ErrorPathDeclMissingEquals) {
  auto r = Parse(
      "module m;\n"
      "  specify\n"
      "    (a => b) 5;\n"
      "  endspecify\n"
      "endmodule\n");
  EXPECT_TRUE(r.has_errors);
}

TEST(SpecifyPathParsing, ErrorPathDeclMissingCloseParen) {
  auto r = Parse(
      "module m;\n"
      "  specify\n"
      "    (a => b = 5;\n"
      "  endspecify\n"
      "endmodule\n");
  EXPECT_TRUE(r.has_errors);
}

TEST(SpecifyPathParsing, ErrorPathDeclMissingOpenParen) {
  auto r = Parse(
      "module m;\n"
      "  specify\n"
      "    a => b) = 5;\n"
      "  endspecify\n"
      "endmodule\n");
  EXPECT_TRUE(r.has_errors);
}

}  // namespace
