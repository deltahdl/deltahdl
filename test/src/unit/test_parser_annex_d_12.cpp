#include <gtest/gtest.h>

#include "fixture_parser.h"

using namespace delta;

namespace {

TEST(OptionalSystemTaskParserParsing, ShowScopesNoArgument) {
  auto r = Parse(
      "module m;\n"
      "  initial $showscopes;\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
}

TEST(OptionalSystemTaskParserParsing, ShowScopesIntegerArgument) {
  auto r = Parse(
      "module m;\n"
      "  initial $showscopes(1);\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
}

}  // namespace
