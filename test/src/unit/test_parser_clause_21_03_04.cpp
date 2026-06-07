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

}
