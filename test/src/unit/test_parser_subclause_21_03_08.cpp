#include "fixture_parser.h"

using namespace delta;

namespace {

// §21.3.8 Syntax 21-11: the detection function in the assignment form shown
// by the standard's example, amid the surrounding open/query/close calls.
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

// §21.3.8 Syntax 21-11: $feof is a function, so beyond the assignment form of
// the standard's example it can sit directly in expression-operand position --
// here guarding a loop and negated inside a condition.
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

// §21.3.8 Syntax 21-11: the detection function may also supply the
// initializer of a variable declaration.
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

// §21.3.8 Syntax 21-11: the fd operand is an expression, not just a plain
// identifier -- an array element or an arithmetic expression may supply the
// descriptor.
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

// §21.3.8 Syntax 21-11: the fd operand may be the result of another function
// call -- here the opening call itself supplies the descriptor directly.
TEST(IoSystemTaskParsing, FeofFdFromFopenCallResult) {
  EXPECT_TRUE(
      ParseOk("module t;\n"
              "  integer e;\n"
              "  initial e = $feof($fopen(\"data.txt\", \"r\"));\n"
              "endmodule\n"));
}

// Negative form: an unterminated $feof call cannot parse.
TEST(IoSystemTaskParsing, UnterminatedFeofRejected) {
  EXPECT_FALSE(
      ParseOk("module t;\n"
              "  integer fd, code;\n"
              "  initial code = $feof(fd;\n"
              "endmodule\n"));
}

}  // namespace
