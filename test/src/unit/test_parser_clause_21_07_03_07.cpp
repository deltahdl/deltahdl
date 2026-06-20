#include "fixture_parser.h"

using namespace delta;

namespace {

// §21.7.3.7: for an extended VCD control task that has only optional arguments,
// the task name may be used with no arguments. $dumpportson takes only an
// optional filename, so the bare form is accepted.
TEST(IoSystemTaskParsing, ExtendedVcdControlTaskBareNoArguments) {
  EXPECT_TRUE(
      ParseOk("module t;\n"
              "  initial $dumpportson;\n"
              "endmodule\n"));
}

// §21.7.3.7: the same task may instead be written as the name followed by an
// empty argument list. Both forms request the default action, so $dumpportson()
// parses just as the bare form does.
TEST(IoSystemTaskParsing, ExtendedVcdControlTaskEmptyArgumentList) {
  EXPECT_TRUE(
      ParseOk("module t;\n"
              "  initial $dumpportson();\n"
              "endmodule\n"));
}

}  // namespace
