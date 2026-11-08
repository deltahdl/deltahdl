#include <gtest/gtest.h>

#include "fixture_parser.h"
#include "helpers_reported_error.h"

using namespace delta;

namespace {

TEST(IoSystemTaskParsing, FreadBasicCall) {
  EXPECT_TRUE(
      ParseOk("module t;\n"
              "  integer fd;\n"
              "  reg [31:0] data;\n"
              "  initial begin\n"
              "    fd = $fopen(\"bin.dat\", \"rb\");\n"
              "    $fread(data, fd);\n"
              "  end\n"
              "endmodule\n"));
}

TEST(IoSystemTaskParsing, FreadWithStartCount) {
  EXPECT_TRUE(
      ParseOk("module t;\n"
              "  integer fd;\n"
              "  reg [7:0] mem [0:255];\n"
              "  initial begin\n"
              "    fd = $fopen(\"bin.dat\", \"rb\");\n"
              "    $fread(mem, fd, 0, 256);\n"
              "  end\n"
              "endmodule\n"));
}

TEST(IoSystemTaskParsing, FreadStartOnlyAndOmittedStartForms) {
  EXPECT_TRUE(
      ParseOk("module t;\n"
              "  integer fd;\n"
              "  reg [7:0] mem [0:255];\n"
              "  initial begin\n"
              "    fd = $fopen(\"bin.dat\", \"rb\");\n"
              "    $fread(mem, fd, 4);\n"
              "    $fread(mem, fd, , 16);\n"
              "  end\n"
              "endmodule\n"));
}

TEST(IoSystemTaskParsing, FreadAsExpressionOperand) {
  EXPECT_TRUE(
      ParseOk("module t;\n"
              "  integer fd;\n"
              "  reg [7:0] mem [0:255];\n"
              "  initial begin\n"
              "    fd = $fopen(\"bin.dat\", \"rb\");\n"
              "    if ($fread(mem, fd) == 0) $display(\"empty\");\n"
              "  end\n"
              "endmodule\n"));
}

TEST(IoSystemTaskParsing, FreadUnterminatedCallRejected) {
  auto r = Parse(
      "module t;\n"
      "  integer fd;\n"
      "  reg [7:0] mem [0:255];\n"
      "  initial $fread(mem, fd;\n"
      "endmodule\n");
  EXPECT_TRUE(ReportedError(r.diags, "expected ')', got ';'", 4, "13.5"));
}

}  // namespace
