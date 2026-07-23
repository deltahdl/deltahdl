// §21.6 Command line input — parse acceptance for the two plusarg query
// functions. Both names carry an embedded '$' ($test$plusargs /
// $value$plusargs); the calls are expressions, so they must parse in every
// expression position: if-conditions, negations, assignment right-hand
// sides, argument positions, and inside task bodies. The first argument may
// be a string literal or a variable; $value$plusargs takes a second,
// destination-variable argument.
#include "fixture_parser.h"

using namespace delta;

namespace {

TEST(PlusargsParsing, TestPlusargsCall) {
  EXPECT_TRUE(
      ParseOk("module t;\n"
              "  initial begin\n"
              "    if ($test$plusargs(\"VERBOSE\"))\n"
              "      $display(\"verbose mode\");\n"
              "  end\n"
              "endmodule\n"));
}

TEST(PlusargsParsing, ValuePlusargsCall) {
  EXPECT_TRUE(
      ParseOk("module t;\n"
              "  integer depth;\n"
              "  initial begin\n"
              "    if ($value$plusargs(\"DEPTH=%d\", depth))\n"
              "      $display(\"depth=%0d\", depth);\n"
              "  end\n"
              "endmodule\n"));
}

// §21.6: the search string may be supplied through a variable rather than a
// literal, for both functions.
TEST(PlusargsParsing, VariablePatternArguments) {
  EXPECT_TRUE(
      ParseOk("module t;\n"
              "  logic [64*8:1] pstring;\n"
              "  logic [8*32:1] testname;\n"
              "  initial begin\n"
              "    if ($test$plusargs(pstring)) $display(\"t\");\n"
              "    if ($value$plusargs(pstring, testname)) $display(\"v\");\n"
              "  end\n"
              "endmodule\n"));
}

// The calls are ordinary expressions: assignment right-hand side and
// system-task argument positions parse.
TEST(PlusargsParsing, CallInAssignmentAndArgumentPositions) {
  EXPECT_TRUE(
      ParseOk("module t;\n"
              "  int r;\n"
              "  initial begin\n"
              "    r = $test$plusargs(\"VERBOSE\");\n"
              "    $display(\"%0d\", $test$plusargs(\"VERBOSE\"));\n"
              "  end\n"
              "endmodule\n"));
}

// Negated-call form used by the LRM's default-value idiom.
TEST(PlusargsParsing, NegatedValuePlusargsCondition) {
  EXPECT_TRUE(
      ParseOk("module t;\n"
              "  real frequency;\n"
              "  initial begin\n"
              "    if (!($value$plusargs(\"FREQ+%0F\", frequency)))\n"
              "      frequency = 8.33333;\n"
              "  end\n"
              "endmodule\n"));
}

// The calls parse inside a task body as well as in an initial process.
TEST(PlusargsParsing, CallInsideTaskBody) {
  EXPECT_TRUE(
      ParseOk("module t;\n"
              "  int v;\n"
              "  task grab;\n"
              "    if ($value$plusargs(\"VAL=%d\", v)) $display(\"%0d\", v);\n"
              "  endtask\n"
              "  initial grab;\n"
              "endmodule\n"));
}

// Negative: an unterminated call is a syntax error.
TEST(PlusargsParsing, UnterminatedTestPlusargsRejected) {
  EXPECT_FALSE(
      ParseOk("module t;\n"
              "  initial begin\n"
              "    if ($test$plusargs(\"VERBOSE\") $display(\"v\");\n"
              "  end\n"
              "endmodule\n"));
}

}  // namespace
