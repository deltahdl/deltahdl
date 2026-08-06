#include "fixture_parser.h"

using namespace delta;

namespace {

// Syntax 21-5: file_output_tasks accept either an mcd or an fd as the first
// argument, and file_output_task_name enumerates all sixteen
// $fdisplay/$fwrite/$fstrobe/$fmonitor variants.

TEST(IoSystemTaskParsing, FdisplayFwrite) {
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

TEST(IoSystemTaskParsing, FstrobeAndFmonitor) {
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

TEST(IoSystemTaskParsing, FileOutputTaskAcceptsMcd) {
  // Syntax 21-5 lets the first argument be a multichannel descriptor.
  EXPECT_TRUE(
      ParseOk("module t;\n"
              "  integer mcd, val;\n"
              "  initial begin\n"
              "    mcd = $fopen(\"channel.log\");\n"
              "    $fdisplay(mcd, \"%d\", val);\n"
              "    $fwrite(mcd, \"raw\");\n"
              "    $fstrobeh(mcd, val);\n"
              "    $fmonitorb(mcd, val);\n"
              "    $fclose(mcd);\n"
              "  end\n"
              "endmodule\n"));
}

TEST(IoSystemTaskParsing, FileOutputTaskNoExtraArguments) {
  // The argument list is optional after the descriptor; a bare descriptor
  // argument is legal under Syntax 21-5.
  EXPECT_TRUE(
      ParseOk("module t;\n"
              "  integer fd;\n"
              "  initial begin\n"
              "    fd = $fopen(\"f.log\", \"w\");\n"
              "    $fdisplay(fd);\n"
              "    $fwrite(fd);\n"
              "    $fclose(fd);\n"
              "  end\n"
              "endmodule\n"));
}

}  // namespace
