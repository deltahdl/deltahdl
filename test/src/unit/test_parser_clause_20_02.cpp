// §20.2: Simulation control system tasks

#include "fixture_parser.h"

using namespace delta;

namespace {

TEST(ParserCh50603, SystemTask_FinishNoArgs) {
  // $finish with no arguments and no parentheses.
  EXPECT_TRUE(ParseOk("module m; initial $finish; endmodule"));
}

}  // namespace
