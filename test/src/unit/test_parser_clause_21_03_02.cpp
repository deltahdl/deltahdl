// §21.3.2: File output system tasks

#include "fixture_parser.h"

using namespace delta;

namespace {

TEST(ParserSection21, FdisplayFwrite) {
  EXPECT_TRUE(
      ParseOk("module t;\n"
              "  integer fd;\n"
              "  initial begin\n"
              "    fd = $fopen(\"log.txt\", \"w\");\n"
              "    $fdisplay(fd, \"value=%d\", 99);\n"
              "    $fwrite(fd, \"no newline\");\n"
              "    $fdisplayb(fd, val);\n"
              "    $fdisplayh(fd, val);\n"
              "    $fdisplayo(fd, val);\n"
              "    $fwriteb(fd, val);\n"
              "    $fwriteh(fd, val);\n"
              "    $fwriteo(fd, val);\n"
              "    $fclose(fd);\n"
              "  end\n"
              "endmodule\n"));
}

}  // namespace
