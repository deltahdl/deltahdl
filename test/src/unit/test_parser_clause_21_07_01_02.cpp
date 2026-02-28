// §21.7.1.2: Specifying variables to be dumped ($dumpvars)

#include "fixture_parser.h"

using namespace delta;

namespace {

TEST(ParserSection21, DumpvarsNoArgs) {
  EXPECT_TRUE(
      ParseOk("module t;\n"
              "  initial $dumpvars;\n"
              "endmodule\n"));
}

TEST(ParserSection21, DumpvarsWithLevels) {
  EXPECT_TRUE(
      ParseOk("module t;\n"
              "  initial $dumpvars(1, t);\n"
              "endmodule\n"));
}

}  // namespace
