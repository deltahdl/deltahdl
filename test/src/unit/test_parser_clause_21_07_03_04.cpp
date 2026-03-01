// §21.7.3.4: Limiting size of dump file ($dumpportslimit)

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
