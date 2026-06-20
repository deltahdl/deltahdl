#include "fixture_parser.h"

using namespace delta;

namespace {

TEST(IoSystemTaskParsing, DumpfileBasic) {
  EXPECT_TRUE(
      ParseOk("module t;\n"
              "  initial $dumpfile(\"dump.vcd\");\n"
              "endmodule\n"));
}

TEST(IoSystemTaskParsing, DumpfileDefaultName) {
  EXPECT_TRUE(
      ParseOk("module t;\n"
              "  initial $dumpfile;\n"
              "endmodule\n"));
}

// The filename slot is a general expression, so a non-literal argument
// such as an identifier must parse, not only a string literal.
TEST(IoSystemTaskParsing, DumpfileExpressionArgument) {
  EXPECT_TRUE(
      ParseOk("module t;\n"
              "  initial $dumpfile(name);\n"
              "endmodule\n"));
}

}  // namespace
