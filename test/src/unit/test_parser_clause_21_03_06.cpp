#include "fixture_parser.h"

using namespace delta;

namespace {

// §21.3.6: file_flush_task ::= $fflush ( [ mcd | fd ] ) ;
// The flush task accepts an optional argument that is either a multi-channel
// descriptor or a single file descriptor; with no argument it flushes all open
// files. Each of the three forms must parse.
TEST(IoSystemTaskParsing, FflushNoArgument) {
  EXPECT_TRUE(
      ParseOk("module t;\n"
              "  initial begin\n"
              "    $fflush();\n"
              "  end\n"
              "endmodule\n"));
}

// The optional argument is a single expression regardless of whether it names
// a multi-channel descriptor or a file descriptor, so one one-argument case
// exercises that grammar branch.
TEST(IoSystemTaskParsing, FflushSingleArgument) {
  EXPECT_TRUE(
      ParseOk("module t;\n"
              "  integer fd;\n"
              "  initial begin\n"
              "    fd = $fopen(\"data.txt\", \"w\");\n"
              "    $fflush(fd);\n"
              "    $fclose(fd);\n"
              "  end\n"
              "endmodule\n"));
}

}  // namespace
