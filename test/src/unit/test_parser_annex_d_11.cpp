#include <gtest/gtest.h>

#include "fixture_parser.h"

using namespace delta;

namespace {

TEST(OptionalSystemTaskParserParsing, Scope) {
  auto r = Parse(
      "module m;\n"
      "  initial $scope(m);\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
}

TEST(OptionalSystemTaskParserParsing, ScopeHierarchicalArgument) {
  auto r = Parse(
      "module m;\n"
      "  initial $scope(m.blk);\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
}

}  // namespace
