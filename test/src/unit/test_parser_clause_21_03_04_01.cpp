// §21.3.4.1: Reading a character at a time

#include "fixture_parser.h"

using namespace delta;

namespace {

// ============================================================================
// LRM section 21.3.4 -- Reading data from a file ($fgetc, $ungetc, $fgets,
//                        $fscanf, $sscanf, $fread)
// ============================================================================
TEST(ParserSection21, FgetcCall) {
  EXPECT_TRUE(
      ParseOk("module t;\n"
              "  integer fd, c;\n"
              "  initial begin\n"
              "    fd = $fopen(\"test.txt\", \"r\");\n"
              "    c = $fgetc(fd);\n"
              "  end\n"
              "endmodule\n"));
}

TEST(ParserSection21, UngetcCall) {
  EXPECT_TRUE(
      ParseOk("module t;\n"
              "  integer fd, code;\n"
              "  initial begin\n"
              "    fd = $fopen(\"test.txt\", \"r\");\n"
              "    code = $ungetc(8'h41, fd);\n"
              "  end\n"
              "endmodule\n"));
}

}  // namespace
