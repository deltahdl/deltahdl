#include "fixture_parser.h"

using namespace delta;

namespace {

// §21.3.5 Syntax 21-8: all three file positioning functions -- $ftell(fd),
// $fseek(fd, offset, operation), and $rewind(fd) -- in assignment and
// statement positions.
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

// §21.3.5 Syntax 21-8: the positioning functions are functions, so each may
// appear as an expression operand, and fd/offset/operation are ordinary
// expressions rather than bare identifiers.
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

// §21.3.5 Syntax 21-8: a positioning function may also supply the initializer
// of a variable declaration.
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

// Negative form: an unterminated $fseek call cannot parse.
TEST(IoSystemTaskParsing, UnterminatedFseekRejected) {
  EXPECT_FALSE(
      ParseOk("module t;\n"
              "  integer fd, code;\n"
              "  initial code = $fseek(fd, 10, 0;\n"
              "endmodule\n"));
}

}  // namespace
