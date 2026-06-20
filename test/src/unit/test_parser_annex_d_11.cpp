#include "fixture_parser.h"
#include "helpers_parser_verify.h"

using namespace delta;

namespace {

// Annex D.11: $scope takes a single hierarchical-name argument and parses as an
// ordinary system task call.
TEST(OptionalSystemTaskParserParsing, Scope) {
  auto r = Parse(
      "module m;\n"
      "  initial $scope(m);\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
}

// Annex D.11: the argument may be a dotted hierarchical name reaching a nested
// scope such as a named block.
TEST(OptionalSystemTaskParserParsing, ScopeHierarchicalArgument) {
  auto r = Parse(
      "module m;\n"
      "  initial $scope(m.blk);\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
}

}  // namespace
