#include <gtest/gtest.h>

#include "fixture_parser.h"

using namespace delta;

namespace {

TEST(IoSystemTaskParsing, ExtendedVcdControlTaskBareNoArguments) {
  EXPECT_TRUE(
      ParseOk("module t;\n"
              "  initial $dumpportson;\n"
              "endmodule\n"));
}

TEST(IoSystemTaskParsing, ExtendedVcdControlTaskEmptyArgumentList) {
  EXPECT_TRUE(
      ParseOk("module t;\n"
              "  initial $dumpportson();\n"
              "endmodule\n"));
}

TEST(IoSystemTaskParsing, DumpportsoffBareAndEmptyParen) {
  EXPECT_TRUE(
      ParseOk("module t;\n"
              "  initial $dumpportsoff;\n"
              "endmodule\n"));
  EXPECT_TRUE(
      ParseOk("module t;\n"
              "  initial $dumpportsoff();\n"
              "endmodule\n"));
}

TEST(IoSystemTaskParsing, DumpportsallBareAndEmptyParen) {
  EXPECT_TRUE(
      ParseOk("module t;\n"
              "  initial $dumpportsall;\n"
              "endmodule\n"));
  EXPECT_TRUE(
      ParseOk("module t;\n"
              "  initial $dumpportsall();\n"
              "endmodule\n"));
}

TEST(IoSystemTaskParsing, DumpportsflushBareAndEmptyParen) {
  EXPECT_TRUE(
      ParseOk("module t;\n"
              "  initial $dumpportsflush;\n"
              "endmodule\n"));
  EXPECT_TRUE(
      ParseOk("module t;\n"
              "  initial $dumpportsflush();\n"
              "endmodule\n"));
}

TEST(IoSystemTaskParsing, NoArgumentSpellingsInOtherStatementPositions) {
  EXPECT_TRUE(
      ParseOk("module t;\n"
              "  task do_flush;\n"
              "    $dumpportsflush;\n"
              "  endtask\n"
              "endmodule\n"));
  EXPECT_TRUE(
      ParseOk("module t;\n"
              "  logic clk;\n"
              "  always @(posedge clk) $dumpportsall();\n"
              "endmodule\n"));
}

}  // namespace
