#include <gtest/gtest.h>

#include "fixture_parser.h"

using namespace delta;

namespace {

TEST(OptionalLogParserParsing, NologNoArgument) {
  auto r = Parse(
      "module m;\n"
      "  initial $nolog;\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
}

TEST(OptionalLogParserParsing, LogNoArgument) {
  auto r = Parse(
      "module m;\n"
      "  initial $log;\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
}

TEST(OptionalLogParserParsing, LogFilenameArgument) {
  auto r = Parse(
      "module m;\n"
      "  initial $log(\"run.log\");\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
}

}  // namespace
