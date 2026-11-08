#include <gtest/gtest.h>

#include "fixture_parser.h"
#include "helpers_reported_error.h"

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

TEST(PlusargsParsing, UnterminatedTestPlusargsRejected) {
  auto result = Parse(
      "module t;\n"
      "  initial begin\n"
      "    if ($test$plusargs(\"VERBOSE\") $display(\"v\");\n"
      "  end\n"
      "endmodule\n");
  EXPECT_TRUE(ReportedError(result.diags, "expected ')', got system identifier",
                            3, "12.4"));
}

}  // namespace
