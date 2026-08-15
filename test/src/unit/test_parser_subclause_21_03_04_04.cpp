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

// §21.3.4.4 example list: start alone, and count alone with start omitted
// via an empty argument slot.
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

// §21.3.4.4: the returned count makes $fread usable inside an expression.
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
  // §13.5 owns the closing parenthesis of a system task call's argument list,
  // so Parser::ParseSystemCall files the report under it rather than under
  // §21.3.4.4.
  EXPECT_TRUE(ReportedError(r.diags, "expected ')', got ';'", 4, "13.5"));
}

}  // namespace
