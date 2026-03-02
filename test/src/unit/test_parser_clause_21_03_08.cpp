// §21.3.8: Detecting EOF

#include "fixture_parser.h"

using namespace delta;

namespace {

TEST(ParserSection21, FeofFerror) {
  EXPECT_TRUE(
      ParseOk("module t;\n"
              "  integer fd, eof_flag;\n"
              "  reg [8*128:1] msg;\n"
              "  initial begin\n"
              "    fd = $fopen(\"data.txt\", \"r\");\n"
              "    eof_flag = $feof(fd);\n"
              "    $ferror(fd, msg);\n"
              "    $fclose(fd);\n"
              "  end\n"
              "endmodule\n"));
}

}  // namespace
