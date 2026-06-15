#include "fixture_parser.h"
#include "helpers_parser_verify.h"

using namespace delta;

namespace {

// Annex D.7: $nolog is invoked with no argument, parsing as an ordinary system
// task call.
TEST(OptionalLogParserParsing, NologNoArgument) {
  auto r = Parse(
      "module m;\n"
      "  initial $nolog;\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
}

// Annex D.7: $log may be invoked with no argument, reenabling log output.
TEST(OptionalLogParserParsing, LogNoArgument) {
  auto r = Parse(
      "module m;\n"
      "  initial $log;\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
}

// Annex D.7: the optional argument to $log is a string literal naming the new
// log file.
TEST(OptionalLogParserParsing, LogFilenameArgument) {
  auto r = Parse(
      "module m;\n"
      "  initial $log(\"run.log\");\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
}

}  // namespace
