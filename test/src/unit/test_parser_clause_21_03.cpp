// §21.3: File input/output system tasks and system functions

#include "fixture_parser.h"

using namespace delta;

namespace {

TEST(ParserSection21, FileIOSequence) {
  EXPECT_TRUE(
      ParseOk("module t;\n"
              "  integer fd, c;\n"
              "  initial begin\n"
              "    fd = $fopen(\"test.txt\", \"r\");\n"
              "    c = $fgetc(fd);\n"
              "    $fseek(fd, 0, 0);\n"
              "    $rewind(fd);\n"
              "    $fflush(fd);\n"
              "    $fclose(fd);\n"
              "  end\n"
              "endmodule\n"));
}

}  // namespace
