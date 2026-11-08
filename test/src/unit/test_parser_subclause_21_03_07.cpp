#include <gtest/gtest.h>

#include "fixture_parser.h"
#include "helpers_reported_error.h"

using namespace delta;

namespace {

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

TEST(IoSystemTaskParsing, UnterminatedFerrorRejected) {
  auto result = Parse(
      "module t;\n"
      "  integer fd, errno;\n"
      "  reg [639:0] msg;\n"
      "  initial errno = $ferror(fd, msg;\n"
      "endmodule\n");
  EXPECT_TRUE(ReportedError(result.diags, "expected ')', got ';'", 4, "13.5"));
}

}  // namespace
