#include "fixture_parser.h"

using namespace delta;

namespace {

// §21.3.4, Syntax 21-7: the file_read_functions production names the family of
// read system functions. Each alternative parses as an ordinary system-function
// call, so the generic call grammar accepts every form of the production.

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

// With both optionals absent, the memory form collapses to two arguments; the
// destination being an unpacked array rather than an integral variable is what
// distinguishes it from the integral form at the call site.
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

// The memory form's start/count arguments are optional; supplying a start
// without a count is a distinct instantiation of the production's grammar.
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

// The nested optional brackets in Syntax 21-7 also permit the start position to
// be skipped while a count is still given, written with an empty argument slot
// between the commas. The system-call grammar accepts the elided argument.
// Every alternative of the production is a system function, so a call is not
// confined to the right-hand side of an assignment: it can sit anywhere an
// expression operand can, e.g. inside a condition.
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

// The production's operands are ordinary expressions, not bare identifiers:
// the descriptor can be an array element, the format a variable, and the
// pushed-back character an arithmetic expression.
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

// The negative form: an argument list left unterminated is not an instance of
// the production and must be rejected by the call grammar.
TEST(FileReadFunctions, UnterminatedReadCallRejected) {
  EXPECT_FALSE(
      ParseOk("module t;\n"
              "  integer fd, c;\n"
              "  initial begin\n"
              "    c = $fgetc(fd;\n"
              "  end\n"
              "endmodule\n"));
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
