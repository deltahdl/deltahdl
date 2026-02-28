// §21.3.4.2: Reading a line at a time

#include "fixture_parser.h"

using namespace delta;

namespace {

TEST(ParserSection21, FgetsCall) {
  EXPECT_TRUE(
      ParseOk("module t;\n"
              "  integer fd, code;\n"
              "  reg [8*80:1] str;\n"
              "  initial begin\n"
              "    fd = $fopen(\"test.txt\", \"r\");\n"
              "    code = $fgets(str, fd);\n"
              "  end\n"
              "endmodule\n"));
}

}  // namespace
