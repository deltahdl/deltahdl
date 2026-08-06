#include "fixture_parser.h"

using namespace delta;

namespace {

// §21.7.3.7: for an extended VCD control task that has only optional
// arguments, the task name may be used with no arguments. $dumpportson takes
// only an optional filename, so the bare form is accepted.
TEST(IoSystemTaskParsing, ExtendedVcdControlTaskBareNoArguments) {
  EXPECT_TRUE(
      ParseOk("module t;\n"
              "  initial $dumpportson;\n"
              "endmodule\n"));
}

// §21.7.3.7: the same task may instead be written as the name followed by an
// empty argument list. Both forms request the default action, so
// $dumpportson() parses just as the bare form does.
TEST(IoSystemTaskParsing, ExtendedVcdControlTaskEmptyArgumentList) {
  EXPECT_TRUE(
      ParseOk("module t;\n"
              "  initial $dumpportson();\n"
              "endmodule\n"));
}

// §21.7.3.7: the rule covers each task of the family -- $dumpportsoff also
// accepts both the bare and the empty-parenthesis spellings.
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

// §21.7.3.7: $dumpportsall accepts both spellings of its no-argument call.
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

// §21.7.3.7: $dumpportsflush -- the clause's own example pair -- accepts both
// spellings of its no-argument call.
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

// §21.7.3.7: the no-argument spellings are ordinary statements, so they parse
// in any statement position -- here a task body carries the bare form and an
// always process the empty-parenthesis form.
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
