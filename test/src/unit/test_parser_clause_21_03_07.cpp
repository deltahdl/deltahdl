#include "fixture_parser.h"

using namespace delta;

namespace {

// §21.3.7: file_error_detect_function ::= $ferror ( fd , str )
// The error-detection function takes a file descriptor and a string variable
// that receives the error description.
TEST(IoSystemTaskParsing, Ferror) {
  EXPECT_TRUE(
      ParseOk("module t;\n"
              "  integer fd, errno;\n"
              "  reg [8*128:1] msg;\n"
              "  initial begin\n"
              "    fd = $fopen(\"data.txt\", \"r\");\n"
              "    errno = $ferror(fd, msg);\n"
              "    $fclose(fd);\n"
              "  end\n"
              "endmodule\n"));
}

}  // namespace
