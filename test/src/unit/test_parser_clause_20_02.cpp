#include "fixture_parser.h"

using namespace delta;

namespace {

TEST(SystemNameParserParsing, SystemTask_FinishNoArgs) {
  EXPECT_TRUE(ParseOk("module m; initial $finish; endmodule"));
}

}  // namespace
