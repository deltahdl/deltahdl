#include <gtest/gtest.h>

#include "fixture_parser.h"
#include "helpers_reported_error.h"

using namespace delta;

namespace {

TEST(IoSystemTaskParsing, AllThreePositioningFunctionsParse) {
  EXPECT_TRUE(
      ParseOk("module t;\n"
              "  integer fd, pos;\n"
              "  initial begin\n"
              "    fd = $fopen(\"data.txt\", \"r\");\n"
              "    pos = $ftell(fd);\n"
              "    $fseek(fd, 10, 0);\n"
              "    $rewind(fd);\n"
              "    $fclose(fd);\n"
              "  end\n"
              "endmodule\n"));
}

TEST(IoSystemTaskParsing, PositioningFunctionsAsExpressionOperands) {
  EXPECT_TRUE(
      ParseOk("module t;\n"
              "  integer fd, base, code;\n"
              "  initial begin\n"
              "    fd = $fopen(\"data.txt\", \"r\");\n"
              "    if ($ftell(fd) == -1) code = 1;\n"
              "    code = $fseek(fd, base + 2, 1 + 1) + $rewind(fd);\n"
              "    while ($fseek(fd, -4, 2) != 0) code = code + 1;\n"
              "    $fclose(fd);\n"
              "  end\n"
              "endmodule\n"));
}

TEST(IoSystemTaskParsing, PositioningFunctionAsDeclarationInitializer) {
  EXPECT_TRUE(
      ParseOk("module t;\n"
              "  integer fd;\n"
              "  initial begin\n"
              "    integer pos = $ftell(fd);\n"
              "    pos = pos + 1;\n"
              "  end\n"
              "endmodule\n"));
}

TEST(IoSystemTaskParsing, UnterminatedFseekRejected) {
  auto r = Parse(
      "module t;\n"
      "  integer fd, code;\n"
      "  initial code = $fseek(fd, 10, 0;\n"
      "endmodule\n");
  EXPECT_TRUE(ReportedError(r.diags, "expected ')', got ';'", 3, "13.5"));
}

}  // namespace
