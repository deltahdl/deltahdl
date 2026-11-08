#include <gtest/gtest.h>

#include "fixture_parser.h"
#include "helpers_reported_error.h"

using namespace delta;

namespace {

TEST(IoSystemTaskParsing, FeofAsAssignmentRhs) {
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

TEST(IoSystemTaskParsing, FeofAsExpressionOperand) {
  EXPECT_TRUE(
      ParseOk("module t;\n"
              "  integer fd, v, r;\n"
              "  initial begin\n"
              "    fd = $fopen(\"data.txt\", \"r\");\n"
              "    while (!$feof(fd)) r = $fscanf(fd, \"%d\", v);\n"
              "    if ($feof(fd) != 0) $display(\"done %0d\", $feof(fd));\n"
              "    $fclose(fd);\n"
              "  end\n"
              "endmodule\n"));
}

TEST(IoSystemTaskParsing, FeofAsDeclarationInitializer) {
  EXPECT_TRUE(
      ParseOk("module t;\n"
              "  integer fd;\n"
              "  initial begin\n"
              "    integer code = $feof(fd);\n"
              "    code = code + 1;\n"
              "  end\n"
              "endmodule\n"));
}

TEST(IoSystemTaskParsing, FeofFdArgumentMayBeExpression) {
  EXPECT_TRUE(
      ParseOk("module t;\n"
              "  integer fd, e;\n"
              "  integer fds [0:1];\n"
              "  initial begin\n"
              "    e = $feof(fds[0]);\n"
              "    e = $feof(fd + 1 - 1);\n"
              "  end\n"
              "endmodule\n"));
}

TEST(IoSystemTaskParsing, FeofFdFromFopenCallResult) {
  EXPECT_TRUE(
      ParseOk("module t;\n"
              "  integer e;\n"
              "  initial e = $feof($fopen(\"data.txt\", \"r\"));\n"
              "endmodule\n"));
}

TEST(IoSystemTaskParsing, UnterminatedFeofRejected) {
  auto result = Parse(
      "module t;\n"
      "  integer fd, code;\n"
      "  initial code = $feof(fd;\n"
      "endmodule\n");
  EXPECT_TRUE(ReportedError(result.diags, "expected ')', got ';'", 3, "13.5"));
}

}  // namespace
