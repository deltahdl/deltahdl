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

TEST(ParserSection21, FstrobeAndFmonitor) {
  EXPECT_TRUE(
      ParseOk("module t;\n"
              "  integer fd;\n"
              "  initial begin\n"
              "    fd = $fopen(\"log.txt\", \"w\");\n"
              "    $fstrobe(fd, \"val=%d\", x);\n"
              "    $fstrobeb(fd, x);\n"
              "    $fstrobeh(fd, x);\n"
              "    $fstrobeo(fd, x);\n"
              "    $fmonitor(fd, \"x=%b\", x);\n"
              "    $fmonitorb(fd, x);\n"
              "    $fmonitorh(fd, x);\n"
              "    $fmonitoro(fd, x);\n"
              "    $fclose(fd);\n"
              "  end\n"
              "endmodule\n"));
}

}  // namespace
