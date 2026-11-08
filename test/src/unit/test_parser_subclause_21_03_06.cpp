#include <gtest/gtest.h>

#include "fixture_parser.h"
#include "helpers_reported_error.h"

using namespace delta;

namespace {

TEST(IoSystemTaskParsing, FflushNoArgument) {
  EXPECT_TRUE(
      ParseOk("module t;\n"
              "  initial begin\n"
              "    $fflush();\n"
              "  end\n"
              "endmodule\n"));
}

TEST(IoSystemTaskParsing, FflushSingleArgument) {
  EXPECT_TRUE(
      ParseOk("module t;\n"
              "  integer fd;\n"
              "  initial begin\n"
              "    fd = $fopen(\"data.txt\", \"w\");\n"
              "    $fflush(fd);\n"
              "    $fclose(fd);\n"
              "  end\n"
              "endmodule\n"));
}

TEST(IoSystemTaskParsing, FflushArgumentExpressionForms) {
  EXPECT_TRUE(
      ParseOk("module t;\n"
              "  parameter integer CON = 1;\n"
              "  integer m1, m2;\n"
              "  integer fds [0:3];\n"
              "  initial begin\n"
              "    $fflush(1);\n"
              "    $fflush(CON);\n"
              "    $fflush(m1 | m2);\n"
              "    $fflush(fds[2]);\n"
              "  end\n"
              "endmodule\n"));
}

TEST(IoSystemTaskParsing, FflushDescriptorFromDeclarationInitializer) {
  EXPECT_TRUE(
      ParseOk("module t;\n"
              "  integer fd = $fopen(\"data.txt\", \"w\");\n"
              "  initial begin\n"
              "    $fflush(fd);\n"
              "    $fclose(fd);\n"
              "  end\n"
              "endmodule\n"));
}

TEST(IoSystemTaskParsing, FflushInTaskBodyAndAlwaysBlock) {
  EXPECT_TRUE(
      ParseOk("module t;\n"
              "  integer fd;\n"
              "  reg clk;\n"
              "  task do_flush;\n"
              "    $fflush(fd);\n"
              "  endtask\n"
              "  always @(posedge clk) $fflush();\n"
              "endmodule\n"));
}

TEST(IoSystemTaskParsing, FflushUnterminatedCallRejected) {
  auto r = Parse(
      "module t;\n"
      "  integer fd;\n"
      "  initial begin\n"
      "    $fflush(fd;\n"
      "  end\n"
      "endmodule\n");
  EXPECT_TRUE(ReportedError(r.diags, "expected ')', got ';'", 4, "13.5"));
}

}  // namespace
