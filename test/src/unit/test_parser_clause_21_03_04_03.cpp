// §21.3.4.3: Reading formatted data

#include "fixture_parser.h"

using namespace delta;

namespace {

TEST(ParserSection21, FscanfCall) {
  EXPECT_TRUE(
      ParseOk("module t;\n"
              "  integer fd, code, val;\n"
              "  initial begin\n"
              "    fd = $fopen(\"data.txt\", \"r\");\n"
              "    code = $fscanf(fd, \"%d\", val);\n"
              "  end\n"
              "endmodule\n"));
}

TEST(ParserSection21, SscanfCall) {
  EXPECT_TRUE(
      ParseOk("module t;\n"
              "  integer code, val;\n"
              "  initial code = $sscanf(\"42\", \"%d\", val);\n"
              "endmodule\n"));
}

}  // namespace
