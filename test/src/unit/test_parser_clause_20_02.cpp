#include "fixture_parser.h"

using namespace delta;

namespace {

TEST(ParserCh50603, SystemTask_FinishNoArgs) {
  EXPECT_TRUE(ParseOk("module m; initial $finish; endmodule"));
}

}  // namespace
