#include "fixture_parser.h"

using namespace delta;

namespace {

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

}
