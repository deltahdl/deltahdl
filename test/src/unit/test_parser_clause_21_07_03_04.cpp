#include "fixture_parser.h"

using namespace delta;

namespace {

TEST(ParserSection21, DumpportslimitCall) {
  EXPECT_TRUE(
      ParseOk("module t;\n"
              "  initial $dumpportslimit(500000);\n"
              "endmodule\n"));
}

}  // namespace
