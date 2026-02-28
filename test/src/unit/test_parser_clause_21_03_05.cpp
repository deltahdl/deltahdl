// §21.3.5: File positioning

#include "fixture_parser.h"

using namespace delta;

namespace {

TEST(ParserSection21, FtellFseek) {
  EXPECT_TRUE(
      ParseOk("module t;\n"
              "  integer fd, pos;\n"
              "  initial begin\n"
              "    fd = $fopen(\"data.txt\", \"r\");\n"
              "    pos = $ftell(fd);\n"
              "    $fseek(fd, 10, 0);\n"
              "    $fclose(fd);\n"
              "  end\n"
              "endmodule\n"));
}

}  // namespace
