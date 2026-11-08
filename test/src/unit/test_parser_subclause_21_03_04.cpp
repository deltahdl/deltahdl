#include <gtest/gtest.h>

#include "fixture_parser.h"
#include "helpers_reported_error.h"

using namespace delta;

namespace {

TEST(FileReadFunctions, FgetcForm) {
  EXPECT_TRUE(
      ParseOk("module t;\n"
              "  integer fd, c;\n"
              "  initial begin\n"
              "    fd = $fopen(\"f.txt\", \"r\");\n"
              "    c = $fgetc(fd);\n"
              "  end\n"
              "endmodule\n"));
}

TEST(FileReadFunctions, UngetcForm) {
  EXPECT_TRUE(
      ParseOk("module t;\n"
              "  integer fd, code;\n"
              "  initial begin\n"
              "    fd = $fopen(\"f.txt\", \"r\");\n"
              "    code = $ungetc(8'h41, fd);\n"
              "  end\n"
              "endmodule\n"));
}

TEST(FileReadFunctions, FgetsForm) {
  EXPECT_TRUE(
      ParseOk("module t;\n"
              "  integer fd, code;\n"
              "  reg [255:0] line;\n"
              "  initial begin\n"
              "    fd = $fopen(\"f.txt\", \"r\");\n"
              "    code = $fgets(line, fd);\n"
              "  end\n"
              "endmodule\n"));
}

TEST(FileReadFunctions, FscanfForm) {
  EXPECT_TRUE(
      ParseOk("module t;\n"
              "  integer fd, code, a, b;\n"
              "  initial begin\n"
              "    fd = $fopen(\"f.txt\", \"r\");\n"
              "    code = $fscanf(fd, \"%d %d\", a, b);\n"
              "  end\n"
              "endmodule\n"));
}

TEST(FileReadFunctions, SscanfForm) {
  EXPECT_TRUE(
      ParseOk("module t;\n"
              "  integer code, a, b;\n"
              "  reg [63:0] src;\n"
              "  initial begin\n"
              "    code = $sscanf(src, \"%d %d\", a, b);\n"
              "  end\n"
              "endmodule\n"));
}

TEST(FileReadFunctions, FreadIntegralForm) {
  EXPECT_TRUE(
      ParseOk("module t;\n"
              "  integer fd, code, val;\n"
              "  initial begin\n"
              "    fd = $fopen(\"f.txt\", \"r\");\n"
              "    code = $fread(val, fd);\n"
              "  end\n"
              "endmodule\n"));
}

TEST(FileReadFunctions, FreadMemoryFormWithStartAndCount) {
  EXPECT_TRUE(
      ParseOk("module t;\n"
              "  integer fd, code;\n"
              "  reg [7:0] mem [0:15];\n"
              "  initial begin\n"
              "    fd = $fopen(\"f.txt\", \"r\");\n"
              "    code = $fread(mem, fd, 0, 8);\n"
              "  end\n"
              "endmodule\n"));
}

TEST(FileReadFunctions, FreadMemoryFormBare) {
  EXPECT_TRUE(
      ParseOk("module t;\n"
              "  integer fd, code;\n"
              "  reg [7:0] mem [0:15];\n"
              "  initial begin\n"
              "    fd = $fopen(\"f.txt\", \"r\");\n"
              "    code = $fread(mem, fd);\n"
              "  end\n"
              "endmodule\n"));
}

TEST(FileReadFunctions, FreadMemoryFormWithStartOnly) {
  EXPECT_TRUE(
      ParseOk("module t;\n"
              "  integer fd, code;\n"
              "  reg [7:0] mem [0:15];\n"
              "  initial begin\n"
              "    fd = $fopen(\"f.txt\", \"r\");\n"
              "    code = $fread(mem, fd, 4);\n"
              "  end\n"
              "endmodule\n"));
}

TEST(FileReadFunctions, ReadCallAsExpressionOperand) {
  EXPECT_TRUE(
      ParseOk("module t;\n"
              "  integer fd;\n"
              "  initial begin\n"
              "    fd = $fopen(\"f.txt\", \"r\");\n"
              "    if ($fgetc(fd) == -1) $display(\"eof\");\n"
              "  end\n"
              "endmodule\n"));
}

TEST(FileReadFunctions, ReadCallOperandsMayBeExpressions) {
  EXPECT_TRUE(
      ParseOk("module t;\n"
              "  integer fds [0:3];\n"
              "  reg [127:0] fmt;\n"
              "  integer a, code;\n"
              "  initial begin\n"
              "    code = $fscanf(fds[1], fmt, a);\n"
              "    code = $ungetc(a + 1, fds[1]);\n"
              "  end\n"
              "endmodule\n"));
}

TEST(FileReadFunctions, UnterminatedReadCallRejected) {
  auto r = Parse(
      "module t;\n"
      "  integer fd, c;\n"
      "  initial begin\n"
      "    c = $fgetc(fd;\n"
      "  end\n"
      "endmodule\n");
  EXPECT_TRUE(ReportedError(r.diags, "expected ')', got ';'", 4, "13.5"));
}

TEST(FileReadFunctions, FreadMemoryFormWithCountButNoStart) {
  EXPECT_TRUE(
      ParseOk("module t;\n"
              "  integer fd, code;\n"
              "  reg [7:0] mem [0:15];\n"
              "  initial begin\n"
              "    fd = $fopen(\"f.txt\", \"r\");\n"
              "    code = $fread(mem, fd, , 8);\n"
              "  end\n"
              "endmodule\n"));
}

}  // namespace
