#include "fixture_parser.h"

using namespace delta;

namespace {

// §21.3.7: file_error_detect_function ::= $ferror ( fd , str )
// The error-detection function takes a file descriptor and a string variable
// that receives the error description.
TEST(IoSystemTaskParsing, FerrorCallParses) {
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

// §21.3.7 Syntax 21-10: $ferror is a function, so it may appear as an
// expression operand, and the str destination may be a string-typed variable.
TEST(IoSystemTaskParsing, FerrorAsExpressionOperandWithStringDest) {
  EXPECT_TRUE(
      ParseOk("module t;\n"
              "  integer fd, code;\n"
              "  string msg;\n"
              "  initial begin\n"
              "    fd = $fopen(\"data.txt\", \"r\");\n"
              "    if ($ferror(fd, msg) != 0) code = 1;\n"
              "    $fclose(fd);\n"
              "  end\n"
              "endmodule\n"));
}

// Negative form: an unterminated $ferror call cannot parse.
TEST(IoSystemTaskParsing, UnterminatedFerrorRejected) {
  EXPECT_FALSE(
      ParseOk("module t;\n"
              "  integer fd, errno;\n"
              "  reg [639:0] msg;\n"
              "  initial errno = $ferror(fd, msg;\n"
              "endmodule\n"));
}

}  // namespace
